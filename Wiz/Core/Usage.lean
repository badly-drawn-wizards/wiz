import Wiz.Core.QPoly

/-!
# Usage vectors

The QTT checker computes, for each subterm, how much it uses each variable in scope.
That is a vector of quantities aligned with the context: here a `List` whose head is
the innermost variable (de Bruijn index 0), matching `Ctx` in `Wiz.Core.Check`.

Each entry is a quantity *polynomial* (`Wiz.Core.QPoly`). Until stage 4d's quantity
variables they are all constants, so you can read `QPoly R` as "a quantity".

Leaving a binder pops the head and compares it against the binder's declared
quantity -- see `popUsage` in `Wiz.Core.Check`.
-/

namespace Wiz

abbrev Usage (R : Type) := List (QPoly R)

namespace Usage

variable {R : Type} [QRig R] [DecidableEq R]

/-- Nothing used, in a context of `n` variables. -/
def zeros (n : Nat) : Usage R := List.replicate n []

/-- The variable at index `ix` used once, in a context of `n` variables. -/
def single (n ix : Nat) : Usage R :=
  (List.range n).map fun i => if i == ix then QPoly.const 1 else []

/-- Pointwise sum: both subterms run. Vectors must have the same length. -/
def add (u v : Usage R) : Usage R := List.zipWith (· + ·) u v

/-- Scale by `q`: the subterm's result is consumed `q` times. -/
def scale (q : QPoly R) (u : Usage R) : Usage R := u.map (q * ·)

instance : Add (Usage R) := ⟨add⟩
instance : HSMul (QPoly R) (Usage R) (Usage R) := ⟨scale⟩

end Usage

end Wiz
