import Wiz.Core.Check
import Wiz.Syntax.Basic

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

variable {R : Type} [QRig R] [DecidableEq R]

structure MetaEntry (R : Type) where
  solution : Option (Val R) := none
  /-- where the hole came from, for "could not infer" errors -/
  info : SourceInfo := {}
  /-- the name of a `?x` hole, or a description like "implicit argument A" -/
  desc : String := "_"

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
  modify fun s => { s with metas := s.metas.push { info := ctx.info, desc } }
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

variable [QuantitySyntax R]

def showTerm (ctx : LocalCtx R) (t : Term R) : String := t.pretty ctx.names

def showVal (ctx : LocalCtx R) (v : Val R) : ElabM R String :=
  return (quote (← getGlobals) ctx.lvl v).pretty ctx.names

end Wiz
