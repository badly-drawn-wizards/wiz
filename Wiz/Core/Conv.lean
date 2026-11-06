import Wiz.Core.Eval

/-!
# Conversion (definitional equality)

`conv l a b` decides whether two values are definitionally equal in a context of `l`
local variables. Because values are already β-normal up to closures, this is mostly a
structural comparison, going under binders with fresh variables.

The interesting case is **η for functions**: `f ≡ λx. f x`. When exactly one side is a
lambda, apply both sides to a fresh variable and compare the results.
-/

namespace Wiz

variable {R : Type} [DecidableEq R]

/-- **Exercise 1.4.** Definitional equality of values.

Cases to handle:
* `sort` vs `sort`: equal levels (no cumulativity yet).
* `pi` vs `pi`: (binder info is irrelevant) equal quantities, convertible domains, convertible codomains under a
  fresh variable. (Should `(x :1 A) → B` and `(x :ω A) → B` be convertible? No --
  subtyping on quantities is a design choice you can revisit later.)
* `lam` vs `lam`, and η: `lam` vs anything, anything vs `lam`.
* `neutral` vs `neutral`: same head, same spine length, pointwise convertible.
* otherwise `false`. -/
partial def conv (g : Globals R) (l : Lvl) : Val R → Val R → Bool
  | a, b => sorry

end Wiz
