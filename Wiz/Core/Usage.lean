import Wiz.Rig

/-!
# Usage vectors

The QTT checker computes, for each subterm, how much it uses each variable in scope.
That is a vector of quantities aligned with the context: here a `List R` whose head is
the innermost variable (de Bruijn index 0), matching `Ctx` in `Wiz.Core.Check`.

Leaving a binder pops the head and compares it against the binder's declared
quantity -- see `popUsage` in `Wiz.Core.Check`.
-/

namespace Wiz

abbrev Usage (R : Type) := List R

namespace Usage

variable {R : Type} [Rig R]

/-- Nothing used, in a context of `n` variables. -/
def zeros (n : Nat) : Usage R := List.replicate n 0

/-- The variable at index `ix` used once, in a context of `n` variables. -/
def single (n ix : Nat) : Usage R :=
  (List.range n).map fun i => if i == ix then 1 else 0

/-- Pointwise sum: both subterms run. Vectors must have the same length. -/
def add (u v : Usage R) : Usage R := List.zipWith (· + ·) u v

/-- Scale by `q`: the subterm's result is consumed `q` times. -/
def scale (q : R) (u : Usage R) : Usage R := u.map (q * ·)

instance : Add (Usage R) := ⟨add⟩
instance : HSMul R (Usage R) (Usage R) := ⟨scale⟩

end Usage

end Wiz
