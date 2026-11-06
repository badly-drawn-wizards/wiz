import Std.Data.HashMap

/-!
# Core terms

The kernel language. Variables are **de Bruijn indices**: `var 0` is the nearest
enclosing binder, `var 1` the next one out, and so on. This makes α-equivalence
syntactic equality and keeps substitution out of the kernel entirely (we never
substitute; see `Wiz.Core.Eval` for normalisation by evaluation).

Names on binders (`x`) are kept only for pretty-printing.

The quantity `q : R` on `pi` and `letE` is the QTT annotation. Lambdas carry no
quantity or domain: they are only ever *checked* against a `pi`, which supplies both.

Not in the core yet (see ROADMAP.md): metavariables (stage 3), μ/ν data (stage 4),
universe polymorphism, Σ-types.
-/

namespace Wiz

abbrev Name := String

inductive Term (R : Type) where
  /-- de Bruijn index -/
  | var (ix : Nat)
  /-- reference to a global declaration -/
  | const (name : Name)
  /-- `Type l`. Non-cumulative for now: `Type l : Type (l+1)` only. -/
  | sort (level : Nat)
  /-- `(x :q dom) → cod`, where `cod` lives under one extra binder -/
  | pi (x : Name) (q : R) (dom cod : Term R)
  /-- `λ x. body`, where `body` lives under one extra binder -/
  | lam (x : Name) (body : Term R)
  | app (fn arg : Term R)
  /-- `let x :q ty := val; body`, where `body` lives under one extra binder -/
  | letE (x : Name) (q : R) (ty val body : Term R)
  /-- `(tm : ty)`, used to switch from checking to inference -/
  | ann (tm ty : Term R)
  deriving Repr, Inhabited, BEq

/-- A global declaration. `value = none` is an axiom/postulate. -/
structure Decl (R : Type) where
  name  : Name
  type  : Term R
  value : Option (Term R)
  deriving Repr, Inhabited

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
