import Wiz.Core.Eval

/-!
# Conversion (definitional equality), type-directed

`conv tys A a b` decides whether `a` and `b`, both of type `A`, are definitionally
equal. `tys` holds the types of the local variables **indexed by level**, so
`tys.size` is the size of the context.

Conversion is **type-directed**: the type is inspected first. That makes the η-rules
easy and complete:

* at a Π type, apply both sides to a fresh variable (η for functions);
* at a Σ type, compare the projections (η for pairs);
* at the unit type, **everything is equal** (η for unit). Without the type you
  couldn't tell that a variable `u : Unit` equals `()`.

Stage 4's observational equality adds one more: at a proposition, all proofs are equal.

Types themselves are compared structurally by `convTy`. Two neutrals are compared by
`convNe`, which walks both spines and **computes the type** as it goes, since the
arguments of an application must be compared at the domain's type.

Reference: Abel & Coquand, *Untyped Algorithmic Equality for Martin-Löf's Logical
Framework with Surjective Pairs* (2007), and the "typed" variant in Abel's habilitation.
-/

namespace Wiz

variable {R : Type} [DecidableEq R]

/-- The type of a neutral's head: a local's type from `tys`, or a global's declared
type with its level parameters instantiated. -/
def headType (g : Globals R) (tys : Array (VTy R)) : Head → Option (VTy R)
  | .local x => tys[x]?
  | .global n us => (g.find? n).map fun d => eval g [] (d.type.instLevels d.levelParams us)
  | .mvar _ => none

mutual

/-- **Exercise 1.4.** Definitional equality of `a` and `b` at type `ty`.

* At a `pi` type: η. Apply both sides to `Val.var tys.size` (with `vApp`) and compare at
  the codomain, with the domain pushed onto `tys`.
* At a `sort`: they are types, so use `convTy`.
* At any other type: both must be neutrals, compared by `convNe`.

**Exercise 4.6** (stage 4b): at a `sigma` type compare the `vFst`s and then the
`vSnd`s (η for pairs); at a `unit` type, always `true`. -/
partial def conv (g : Globals R) (tys : Array (VTy R)) (ty : VTy R) (a b : Val R) : Bool :=
  sorry

/-- **Exercise 1.4b.** Equality of two types.

* `sort`/`sort`: `Level.equiv`.
* `pi`/`pi`: equal quantities (binder info is irrelevant), convertible domains, and
  convertible codomains under a fresh variable of the domain type.
* Two neutrals: `convNe`.
* Otherwise `false`.

**Exercise 4.6b** (stage 4b): `sigma`/`sigma` like `pi`; `unit`/`unit` and
`empty`/`empty` by `Level.equiv`. -/
partial def convTy (g : Globals R) (tys : Array (VTy R)) (a b : VTy R) : Bool :=
  sorry

/-- **Exercise 1.4c.** Compare two neutrals. On success return their (common) type.

Heads must be `Head.equiv` and spines the same length. Start from the head's type
(`headType`) and walk both spines together, keeping the current type and the value
of the neutral so far:

* `app a`, `app b` at type `(x : A) → B`: `conv` the arguments at `A`; the new type is
  `B` instantiated with `a`.

**Exercise 4.6c** (stage 4b):
* `fst` at `(x : A) × B`: type `A`. `snd`: type `B` instantiated with the first
  projection of the neutral so far.
* `split` at `(x : A) × B`: equal quantities, motives `convTy` under a binder of
  the Σ type, and bodies `conv` under binders `x : A` and `y : B x` at the
  motive instantiated with `(x, y)`. The result type is the motive at the neutral.
* `absurd m`: motives `convTy`; the result type is `m`. -/
partial def convNe (g : Globals R) (tys : Array (VTy R)) (a b : Val R) : Option (VTy R) := do
  sorry

end

end Wiz
