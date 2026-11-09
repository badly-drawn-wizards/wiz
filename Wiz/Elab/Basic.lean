import Wiz.Core.Check
import Wiz.Syntax.Basic
import Wiz.Compiler.Run

/-!
# The elaborator monad

The elaborator turns surface `Syntax` into core `Term`s. Users leave out a lot
(implicit arguments, the types of `fun` binders, `_` holes), and the elaborator fills
it in with **metavariables**, holes that unification solves.

## Metavariables

Following Kovács' elaboration-zoo, metavariables are **closed**. A hole in a context
`Γ = x₁ … xₙ` becomes `?m x₁ … xₙ`, the metavariable applied to every *bound*
variable in scope (not the `let`-bound ones, whose values are known). A solution is
then a closed function `fun x₁ … xₙ => rhs`. This makes scoping explicit and lets the
kernel's evaluator handle metas as ordinary stuck neutrals (`Head.mvar`).

Metas are untyped here, because the stage 1 kernel re-checks every elaborated
declaration. The elaborator only has to produce *candidates*; the kernel is the
trusted judge (the "de Bruijn criterion"). Quantities are likewise left to the
kernel.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

structure MetaEntry (R : Type) where
  solution : Option (Val R) := none
  /-- where the hole came from, for "could not infer" errors -/
  info : SourceInfo := {}
  /-- the name of a `?x` hole, or a description like "implicit argument A" -/
  desc : String := "_"
  /-- how many bound variables it is applied to -/
  arity : Nat := 0

/-- A type class: its parameters' output flags (`outParam`) and its fields, in order. -/
structure ClassInfo where
  name : Name
  outParams : List Bool
  fields : List Name
  deriving Inhabited

/-- An instance: a global whose type ends in an application of `cls`. Later instances
and higher priorities are tried first. -/
structure InstanceInfo where
  name : Name
  cls : Name
  priority : Nat := 1000
  deriving Inhabited

structure ElabError where
  info : SourceInfo
  msg : String
  deriving Inhabited, Repr

/-- The local context. As in `Ctx`, the lists are aligned and index 0 is innermost. -/
structure LocalCtx (R : Type) where
  env : Env R := []
  names : List Name := []
  types : List (VTy R) := []
  /-- `true` for λ/Π-bound variables, `false` for `let`-bound ones -/
  bound : List Bool := []
  lvl : Lvl := 0
  /-- the syntax being elaborated, for error positions -/
  info : SourceInfo := {}
  /-- variables known to be erased (constructor fields of quantity 0): a `match` that
  reverts one binds it at quantity 0 again -/
  erasedLvls : List Lvl := []

structure ElabState (R : Type) where
  globals : Globals R
  metas : Array (MetaEntry R) := #[]
  /-- level metavariables and their solutions -/
  levelMetas : Array (Option Level) := #[]
  /-- the universe level parameters of the declaration being elaborated -/
  levelParams : List Name := []
  /-- "the solution of this hole has type `Sort l`". Metas are untyped, so these are
  checked after elaboration to solve level metavariables (see `solveSortConstraints`). -/
  sortConstraints : Array (LocalCtx R × Term R × Level) := #[]
  /-- macro rules in scope, latest first: (kind, pattern, template, notation vars) -/
  macros : List (Name × Syntax × Syntax × List Name) := []
  /-- the next fresh macro scope -/
  nextScope : Nat := 1
  /-- `builtin key := name` registrations (numerals need the `nat` type) -/
  builtins : List (Name × Name) := []
  /-- procedural macros: node kind and the Wiz function that expands it, latest first -/
  procMacros : List (Name × Name) := []
  /-- runs a procedural macro (`f`, the node, the next scope); the command elaborator
  supplies it, since it needs the compiler -/
  runProcMacro : Name → Syntax → Nat → Except String (Syntax × Nat) :=
    fun _ _ _ => .error "procedural macros can't run here"
  /-- tactics: node kind and the Wiz function that runs it, latest first -/
  tactics : List (Name × Name) := []
  /-- erase what is reachable from these globals, for the interpreter (supplied by the
  command elaborator) -/
  compileCode : List Name → Except String Code := fun _ => .error "tactics can't run here"
  /-- type classes and instances in scope (stage 7) -/
  classes : List ClassInfo := []
  instances : Array InstanceInfo := #[]
  /-- for the language server: identifiers, where they are, and their types (stage 11) -/
  hovers : Array (SourceInfo × Name × String) := #[]
  /-- instance problems not solved yet: the hole, in its context, and its class type -/
  pendingInsts : Array (LocalCtx R × Term R × VTy R) := #[]
  /-- the kernel's type inference, for complete terms (supplied by the command elaborator) -/
  kernelInfer : Ctx R → Term R → Except String (VTy R) := fun _ _ => .error "no kernel here"

abbrev ElabM (R : Type) := StateT (ElabState R) (Except ElabError)

namespace LocalCtx

def bind (ctx : LocalCtx R) (x : Name) (ty : VTy R) : LocalCtx R :=
  { ctx with
    env := Val.var ctx.lvl :: ctx.env, names := x :: ctx.names, types := ty :: ctx.types
    bound := true :: ctx.bound, lvl := ctx.lvl + 1 }

def define (ctx : LocalCtx R) (x : Name) (ty : VTy R) (val : Val R) : LocalCtx R :=
  { ctx with
    env := val :: ctx.env, names := x :: ctx.names, types := ty :: ctx.types
    bound := false :: ctx.bound, lvl := ctx.lvl + 1 }

def withInfo (ctx : LocalCtx R) (stx : Syntax) : LocalCtx R :=
  if stx.info.stop == 0 then ctx else { ctx with info := stx.info }

end LocalCtx

def throwAt (info : SourceInfo) (msg : String) : ElabM R α := throw { info, msg }

def getGlobals : ElabM R (Globals R) := return (← get).globals

def evalIn (ctx : LocalCtx R) (t : Term R) : ElabM R (Val R) :=
  return eval (← getGlobals) ctx.env t

/-! ### Sorts of the `Π`/`Σ` types the elaborator builds

A `Π`/`Σ` carries its sort so that type equality can tell propositions (compared by
equivalence) from other types (compared by shape); without one, an equation between
two such types stays stuck. Surface `Π`/`Σ` get theirs from `checkType`'s levels. The
ones the elaborator builds itself (a definition's telescope, constructor types,
recursors, match motives, …) get theirs here, from the kernel's `typeSort?` in the
context where the type lives. A sort is only written when it is known: the kernel
rejects a wrong one (`checkSortNote`), and an unknown one (a metavariable, or a
variable whose type isn't known) leaves `none`. -/
namespace Sorts
variable (g : Globals R)

mutual
/-- `t` is a type in the context `tys`/`env` (types by level, values innermost
first): fill in the missing sorts in it, and return its sort when it is known. -/
partial def type (tys : Array (VTy R)) (env : Env R) : Term R → Term R × Option Level
  | .pi x bi q A B s =>
    let (A, lA) := type tys env A
    let (B, lB) := type (tys.push (eval g env A)) (Val.var tys.size :: env) B
    let s := s.orElse fun _ => return .imax (← lA) (← lB)
    (.pi x bi (term tys env q) A B s, s)
  | .sigma x q A B s =>
    let (A, lA) := type tys env A
    let (B, lB) := type (tys.push (eval g env A)) (Val.var tys.size :: env) B
    let s := s.orElse fun _ => return .max (← lA) (← lB)
    (.sigma x (term tys env q) A B s, s)
  | t =>
    let t := term tys env t
    (t, typeSort? g tys (eval g env t))

/-- Fill in the missing sorts of the `Π`/`Σ` types in `t`, as far as the types of the
variables are known: not under binders other than `Π`, `Σ` and `let` (a `fun`'s
variable has no type written down; see `value`). -/
partial def term (tys : Array (VTy R)) (env : Env R) : Term R → Term R
  | t@(.pi ..) | t@(.sigma ..) => (type tys env t).1
  | .letE x q T v b =>
    let T := (type tys env T).1
    let v := term tys env v
    .letE x (term tys env q) T v (term (tys.push (eval g env T)) (eval g env v :: env) b)
  | t => Id.run <| t.mapChildrenM pure fun k c => pure (if k == 0 then term tys env c else c)

/-- `t` has type `ty`: like `term`, also under the `fun`s that `ty` gives types to. -/
partial def value (tys : Array (VTy R)) (env : Env R) (t : Term R) (ty : VTy R) : Term R :=
  match t, whnf ty with
  | .lam x b, .pi _ _ _ A B _ =>
    let v := Val.var tys.size
    .lam x (value (tys.push A) (v :: env) b (Closure.inst g B v))
  | t, _ => term tys env t
end

end Sorts

/-- `Sorts.type` in a local context. -/
def LocalCtx.sortType (g : Globals R) (ctx : LocalCtx R) (t : Term R) : Term R :=
  (Sorts.type g ctx.types.reverse.toArray ctx.env t).1

/-- A `Π`/`Σ` value in a local context with its sort filled in, when it is known. -/
def LocalCtx.sortVal (g : Globals R) (ctx : LocalCtx R) (v : Val R) : Val R :=
  match v with
  | .pi x bi q A B none => .pi x bi q A B (typeSort? g ctx.types.reverse.toArray v)
  | .sigma x q A B none => .sigma x q A B (typeSort? g ctx.types.reverse.toArray v)
  | v => v

/-- A declaration with the sorts of its types filled in (`Sorts`). -/
def Decl.withSorts (g : Globals R) (d : Decl R) : Decl R :=
  let type := (Sorts.type g #[] [] d.type).1
  let ty := eval g [] type
  { d with type, value := d.value.map (Sorts.value g #[] [] · ty),
           impl := d.impl.map (Sorts.value g #[] [] · ty) }

def instM (c : Closure R) (v : Val R) : ElabM R (Val R) :=
  return Closure.inst (← getGlobals) c v

def vAppM (f a : Val R) : ElabM R (Val R) := return vApp (← getGlobals) f a

def lookupMeta (m : Nat) : ElabM R (MetaEntry R) := do
  match (← get).metas[m]? with
  | some e => pure e
  | none => throwAt {} s!"internal error: unknown metavariable ?m{m}"

def solveMeta (m : Nat) (v : Val R) : ElabM R Unit :=
  modify fun s => { s with metas := s.metas.modify m ({ · with solution := some v }) }

/-- A fresh metavariable applied to all the bound variables of `ctx`. -/
def freshMeta (ctx : LocalCtx R) (desc : String := "_") : ElabM R (Term R) := do
  let m := (← get).metas.size
  let arity := (ctx.bound.filter id).length
  modify fun s => { s with metas := s.metas.push { info := ctx.info, desc, arity } }
  -- `bound` is innermost first; walk it from the outside in, i.e. by level
  let flags := ctx.bound.reverse
  let mut t : Term R := .mvar m
  for b in flags, lvl in [0:ctx.lvl] do
    if b then t := .app t (.var (ctx.lvl - lvl - 1))
  pure t

/-- Record that the hole `t` (in `ctx`) must have type `Sort l`. -/
def addSortConstraint (ctx : LocalCtx R) (t : Term R) (l : Level) : ElabM R Unit :=
  modify fun s => { s with sortConstraints := s.sortConstraints.push (ctx, t, l) }

def freshLevelMeta : ElabM R Level := do
  let m := (← get).levelMetas.size
  modify fun s => { s with levelMetas := s.levelMetas.push none }
  pure (.mvar m)

/-- Replace solved level metavariables. -/
def instLevel (l : Level) : ElabM R Level := do
  let ls := (← get).levelMetas
  pure (l.instMVars fun m => ls[m]?.join)


def showTerm (ctx : LocalCtx R) (t : Term R) : String := t.pretty ctx.names

def showVal (ctx : LocalCtx R) (v : Val R) : ElabM R String :=
  return (quote (← getGlobals) ctx.lvl v).pretty ctx.names

end Wiz
