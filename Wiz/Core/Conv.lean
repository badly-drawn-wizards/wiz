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

variable {R : Type} [QRig R] [DecidableEq R]

/-- The type of a neutral's head: a local's type from `tys`, a global's declared type
with its level parameters instantiated, or (stage 4c) the type of a stuck
observational construct. -/
def headType (g : Globals R) (tys : Array (VTy R)) : Head R → Option (VTy R)
  | .local x => tys[x]?
  | .global n us => (g.find? n).map fun d => eval g [] (d.type.instLevels d.levelParams us)
  | .mvar _ => none
  | .eq .. | .eqTy .. => some (.sort 0)
  | .cast _ B _ _ => some B
  | .refl A a => some (vEq g A a a)
  | .reflTy X => some (vEqType g X X)
  | .transp _ _ P _ b e => some (vApp g (vApp g P b) e)

/-- The type of a neutral, computed by walking its spine from the head's type. -/
def inferNe (g : Globals R) (tys : Array (VTy R)) : Val R → Option (VTy R)
  | .neutral h sp => do
    let mut ty ← headType g tys h
    let mut acc : Val R := .neutral h #[]
    for e in sp do
      match e, ty with
      | .app x, .pi _ _ _ _ cod => ty := Closure.inst g cod x; acc := vApp g acc x
      | .fst, .sigma _ _ A _ => ty := A; acc := vFst acc
      | .snd, .sigma _ _ _ B => ty := Closure.inst g B (vFst acc); acc := vSnd acc
      | .split q z m x y b, _ => ty := Closure.inst g m acc; acc := vSplit g q acc z m x y b
      | .absurd m, _ => ty := m; acc := vAbsurd m acc
      | _, _ => none
    pure ty
  | _ => none

/-- The universe level of a type, if it can be computed. -/
partial def typeSort? (g : Globals R) (tys : Array (VTy R)) : VTy R → Option Level
  | .sort l => some (.succ l)
  | .pi _ _ _ A B => do
    return .imax (← typeSort? g tys A) (← typeSort? g (tys.push A) (Closure.inst g B (Val.var tys.size)))
  | .sigma _ _ A B => do
    return .max (← typeSort? g tys A) (← typeSort? g (tys.push A) (Closure.inst g B (Val.var tys.size)))
  | .unit l | .empty l => some l
  | .qty => some 1
  | v@(.neutral ..) => do
    match ← inferNe g tys v with
    | .sort l => some l
    | _ => none
  | _ => none

/-- Is this type a proposition? Then all its inhabitants are equal. -/
def isProp (g : Globals R) (tys : Array (VTy R)) (ty : VTy R) : Bool :=
  match typeSort? g tys ty with
  | some l => l.equiv 0
  | none => false

mutual

/-- **Exercise 1.4.** Definitional equality of `a` and `b` at type `ty`.

* At a `pi` type: η. Apply both sides to `Val.var tys.size` (with `vApp`) and compare at
  the codomain, with the domain pushed onto `tys`.
* At a `sort`: they are types, so use `convTy`.
* At any other type: both must be neutrals, compared by `convNe`.

**Exercise 4.6** (stage 4b): at a `sigma` type compare the `vFst`s and then the
`vSnd`s (η for pairs); at a `unit` type, always `true`.

**Exercise 4.13** (stage 4c): first, **proof irrelevance**: if `isProp ty`, return
`true`. Then **regularity**: a stuck `cast A B e t` with an empty spine and
`convTy A B` is replaced by `t` (on either side) before comparing. -/
partial def conv (g : Globals R) (tys : Array (VTy R)) (ty : VTy R) (a b : Val R) : Bool :=
  sorry

/-- **Exercise 1.4b.** Equality of two types.

* `sort`/`sort`: `Level.equiv`.
* `pi`/`pi`: equal quantities (binder info is irrelevant), convertible domains, and
  convertible codomains under a fresh variable of the domain type. (Stage 4c: when
  the type is a proposition, quantities don't matter, since proofs are erased.)
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

**Exercise 4.13b** (stage 4c): heads that contain values. `eq`: compare the types with
`convTy` and the sides with `conv`; `eqTy`: `convTy` both; `cast`: the types and the
casted terms; two proof heads (`refl`, `reflTy`, `transp`) are always equal.

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
