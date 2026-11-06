import Std.Data.HashMap
import Wiz.Core.Level

/-!
# Core terms

The kernel language. Variables are **de Bruijn indices**: `var 0` is the nearest
enclosing binder, `var 1` the next one out, and so on. This makes α-equivalence
syntactic equality and keeps substitution out of the kernel entirely (we never
substitute; see `Wiz.Core.Eval` for normalisation by evaluation).

Names on binders (`x`) are kept only for pretty-printing.

The quantity `q : R` on `pi` and `letE` is the QTT annotation. Lambdas carry no
quantity or domain: they are only ever *checked* against a `pi`, which supplies both.

`BinderInfo` on `pi` says whether the argument is explicit or implicit. The kernel
ignores it; the elaborator uses it to insert implicit arguments.

`mvar` is a metavariable, a hole the elaborator (stage 3) is still solving. The kernel
evaluates it to a stuck neutral and rejects it in the type checker. Elaborated terms
have all their metavariables replaced before they reach the kernel.

Universe levels are described in `Wiz.Core.Level`.

Not in the core yet (see ROADMAP.md): μ/ν data and Σ-types (stage 4).
-/

namespace Wiz

abbrev Name := String

inductive BinderInfo where
  | default
  | implicit
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Term (R : Type) where
  /-- de Bruijn index -/
  | var (ix : Nat)
  /-- a global declaration, with its universe level parameters instantiated -/
  | const (name : Name) (levels : List Level)
  /-- `Sort l` (`Prop` is `Sort 0`, `Type u` is `Sort (u+1)`). Non-cumulative:
  `Sort l : Sort (l+1)` only. -/
  | sort (level : Level)
  /-- `(q x : dom) → cod` (or `{q x : dom} → cod`), where `cod` lives under one extra
  binder -/
  | pi (x : Name) (bi : BinderInfo) (q : R) (dom cod : Term R)
  /-- `λ x. body`, where `body` lives under one extra binder -/
  | lam (x : Name) (body : Term R)
  | app (fn arg : Term R)
  /-- `let x :q ty := val; body`, where `body` lives under one extra binder -/
  | letE (x : Name) (q : R) (ty val body : Term R)
  /-- `(tm : ty)`, used to switch from checking to inference -/
  | ann (tm ty : Term R)
  /-- metavariable number `id` (elaborator only) -/
  | mvar (id : Nat)
  -- Stage 4: structural types. `sigma` binder names double as field names.
  /-- `(q x : A) × B`: the first component may be used `q` times -/
  | sigma (x : Name) (q : R) (fst snd : Term R)
  | pair (a b : Term R)
  | fst (t : Term R)
  | snd (t : Term R)
  /-- `let q (x, y) := scrut; body` with motive `fun z => motive` for the result type.
  `motive` is under one binder (`z`), `body` under two (`x`, then `y`). -/
  | split (q : R) (scrut : Term R) (z : Name) (motive : Term R) (x y : Name) (body : Term R)
  /-- the unit type in `Sort l`: `True` at level 0, `Unit` at level 1 -/
  | unit (level : Level)
  | tt
  /-- the empty type in `Sort l`: `False` at level 0, `Empty` at level 1 -/
  | empty (level : Level)
  /-- `absurd t : motive`, given `t : empty l` -/
  | absurd (motive t : Term R)
  deriving Repr, Inhabited, BEq

/-- A global declaration. `value = none` is an axiom/postulate. -/
structure Decl (R : Type) where
  name  : Name
  /-- universe level parameters, e.g. `[u]` for `def id.{u} ...` -/
  levelParams : List Name := []
  type  : Term R
  value : Option (Term R)
  deriving Repr, Inhabited

namespace Term

variable {R : Type}

/-- Instantiate universe level parameters `ps` with `us`. -/
def instLevels (ps : List Name) (us : List Level) : Term R → Term R
  | .sort l => .sort (l.instParams ps us)
  | .const n ls => .const n (ls.map (·.instParams ps us))
  | .pi x bi q a b => .pi x bi q (instLevels ps us a) (instLevels ps us b)
  | .lam x b => .lam x (instLevels ps us b)
  | .app f a => .app (instLevels ps us f) (instLevels ps us a)
  | .letE x q t v b => .letE x q (instLevels ps us t) (instLevels ps us v) (instLevels ps us b)
  | .ann t ty => .ann (instLevels ps us t) (instLevels ps us ty)
  | .sigma x q a b => .sigma x q (instLevels ps us a) (instLevels ps us b)
  | .pair a b => .pair (instLevels ps us a) (instLevels ps us b)
  | .fst t => .fst (instLevels ps us t)
  | .snd t => .snd (instLevels ps us t)
  | .split q s z m x y b =>
    .split q (instLevels ps us s) z (instLevels ps us m) x y (instLevels ps us b)
  | .unit l => .unit (l.instParams ps us)
  | .empty l => .empty (l.instParams ps us)
  | .absurd m t => .absurd (instLevels ps us m) (instLevels ps us t)
  | t => t

/-- All level parameter names mentioned in a term. -/
def levelParamsUsed : Term R → List Name
  | .sort l => l.params
  | .const _ ls => ls.flatMap Level.params
  | .pi _ _ _ a b | .app a b | .ann a b => levelParamsUsed a ++ levelParamsUsed b
  | .lam _ b => levelParamsUsed b
  | .letE _ _ t v b => levelParamsUsed t ++ levelParamsUsed v ++ levelParamsUsed b
  | .sigma _ _ a b | .pair a b | .absurd a b => levelParamsUsed a ++ levelParamsUsed b
  | .fst t | .snd t => levelParamsUsed t
  | .split _ s _ m _ _ b => levelParamsUsed s ++ levelParamsUsed m ++ levelParamsUsed b
  | .unit l | .empty l => l.params
  | _ => []

end Term

/-- The global environment. `order` records insertion order so anything that walks
the environment does so deterministically (never iterate the hash map directly). -/
structure Globals (R : Type) where
  decls : Std.HashMap Name (Decl R) := {}
  order : Array Name := #[]

namespace Globals

variable {R : Type}

def find? (g : Globals R) (n : Name) : Option (Decl R) := g.decls[n]?

def contains (g : Globals R) (n : Name) : Bool := g.decls.contains n

/-- Unchecked insertion. Use `Wiz.addDecl` to type check first. -/
def insert (g : Globals R) (d : Decl R) : Globals R :=
  { decls := g.decls.insert d.name d
    order := if g.decls.contains d.name then g.order else g.order.push d.name }

end Globals

end Wiz
