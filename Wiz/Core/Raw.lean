import Wiz.Core.Term

/-!
# Named terms

Until the parser exists (stage 2 in ROADMAP.md) we write programs as `Raw` terms
with named variables, and `Raw.toTerm` resolves them to de Bruijn indices. A name that
isn't bound locally is assumed to be a global `const`. The checker reports it if it
doesn't exist.

The small DSL at the bottom keeps test programs readable.
-/

namespace Wiz

inductive Raw (R : Type) where
  | var (x : Name)
  | sort (level : Nat)
  | pi (x : Name) (q : R) (dom cod : Raw R)
  | lam (x : Name) (body : Raw R)
  | app (fn arg : Raw R)
  | letE (x : Name) (q : R) (ty val body : Raw R)
  | ann (tm ty : Raw R)
  deriving Repr, Inhabited

namespace Raw

variable {R : Type}

/-- Resolve names. `scope` lists bound names, innermost first. -/
def toTerm (scope : List Name := []) : Raw R → Term R
  | .var x => match scope.idxOf? x with
    | some ix => .var ix
    | none => .const x
  | .sort l => .sort l
  | .pi x q a b => .pi x q (a.toTerm scope) (b.toTerm (x :: scope))
  | .lam x b => .lam x (b.toTerm (x :: scope))
  | .app f a => .app (f.toTerm scope) (a.toTerm scope)
  | .letE x q t v b => .letE x q (t.toTerm scope) (v.toTerm scope) (b.toTerm (x :: scope))
  | .ann t ty => .ann (t.toTerm scope) (ty.toTerm scope)

/-! ## DSL -/

instance : Coe String (Raw R) := ⟨.var⟩

/-- `Type` -/
def ty : Raw R := .sort 0

/-- `λ x y z. b` -/
def lams (xs : List Name) (b : Raw R) : Raw R := xs.foldr .lam b

/-- `f a b c` -/
def apps (f : Raw R) (args : List (Raw R)) : Raw R := args.foldl .app f

/-- `(x :q A) → B` -/
def pi' (x : Name) (q : R) (a b : Raw R) : Raw R := .pi x q a b

/-- `A →q B` (non-dependent) -/
def arr (q : R) (a b : Raw R) : Raw R := .pi "_" q a b

end Raw

/-- A named declaration: `def name : type := value`. -/
def Raw.defn {R : Type} (name : Name) (type value : Raw R) : Decl R :=
  { name, type := type.toTerm, value := some value.toTerm }

/-- `axiom name : type` -/
def Raw.axiom {R : Type} (name : Name) (type : Raw R) : Decl R :=
  { name, type := type.toTerm, value := none }

end Wiz
