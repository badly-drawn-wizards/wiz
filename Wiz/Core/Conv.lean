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

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

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

/-! ### Types of the data eliminators' arguments (stage 4d)

Built as terms in a small environment and evaluated, like the templates. `w` is the
quantity to put on the binders: the kernel uses the rig's default, and conversion
(which only needs the types to direct η) passes anything. -/

private def tv (i : Nat) : Term R := .var i
private def tapps (f : Term R) (as : List (Term R)) : Term R := as.foldl .app f

/-- `P : Desc I → Sort v` -/
def delimMotiveTy (l v : Level) (I : Val R) (w : R) : VTy R :=
  .pi "D" .default (.qlit w) (.desc l I) (.mk [] (.sort v))

/-- The types of `mret`, `marg`, `mrec` for `Desc.elim` with motive `P`. -/
def delimMethodTys (g : Globals R) (l : Level) (I P : Val R) (w : R) : VTy R × VTy R × VTy R :=
  let pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit w) a b
  let env := [P, I]
  -- i0 P1 I2
  let mret := pi "i" (tv 1) (.app (tv 1) (.dret (tv 0)))
  -- q0 P1 I2 ; S0 q1 P2 I3 ; E0 S1 q2 P3 I4 ; ih0 E1 S2 q3 P4 I5
  let marg := pi "q" .qty (pi "S" (.sort (.succ l)) (pi "E" (pi "s" (tv 0) (.desc l (tv 4)))
    (pi "ih" (pi "s" (tv 1) (.app (tv 4) (.app (tv 1) (tv 0)))) (.app (tv 4) (.darg (tv 3) (tv 2) (tv 1))))))
  -- q0 P1 I2 ; j0 q1 P2 I3 ; E0 j1 q2 P3 I4 ; ih0 E1 j2 q3 P4 I5
  let mrec := pi "q" .qty (pi "j" (tv 2) (pi "E" (.desc l (tv 3))
    (pi "ih" (.app (tv 3) (tv 0)) (.app (tv 4) (.drec (tv 3) (tv 2) (tv 1))))))
  (eval g env mret, eval g env marg, eval g env mrec)

/-- `P : (i : I) → μ D i → Sort v` -/
def indMotiveTy (g : Globals R) (l v : Level) (I D : Val R) (w : R) : VTy R :=
  eval g [D, I] (.pi "i" .default (.qlit w) (tv 1)
    (.pi "_" .default (.qlit w) (.mu l (tv 2) (tv 1) (tv 0) .szInf none) (.sort v)))

/-- `m : (0 i : I) → (xs : ⟦D⟧ (μ D) i) → (ih : All D (μ D) P i xs) → P i (con xs)` -/
def indMethodTy (g : Globals R) (l v : Level) (I D P : Val R) (w : R) : VTy R :=
  -- i0 P1 D2 I3 ; xs0 i1 P2 D3 I4 ; ih0 xs1 i2 P3 D4 I5
  let X₁ : Term R := .lam "j" (.mu l (tv 4) (tv 3) (tv 0) .szInf none)
  let X₂ : Term R := .lam "j" (.mu l (tv 5) (tv 4) (tv 0) .szInf none)
  eval g [P, D, I] (.pi "i" .default (.qlit 0) (tv 2)
    (.pi "xs" .default (.qlit w) (tapps (Templates.interpTm l) [tv 3, tv 2, X₁, tv 0])
      (.pi "ih" .default (.qlit w) (tapps (Templates.allTm l v) [tv 4, tv 3, X₂, tv 2, tv 1, tv 0])
        (tapps (tv 3) [tv 2, .con (tv 1)]))))

/-- `S : I → Type l` -/
def coitStateTy (l : Level) (I : Val R) (w : R) : VTy R :=
  .pi "i" .default (.qlit w) I (.mk [] (.sort (.succ l)))

/-- `step : (i : I) → S i → ⟦D⟧ S i` -/
def coitStepTy (g : Globals R) (l : Level) (I D S : Val R) (w : R) : VTy R :=
  -- i0 S1 D2 I3 ; s0 i1 S2 D3 I4
  eval g [S, D, I] (.pi "i" .default (.qlit w) (tv 2)
    (.pi "s" .default (.qlit w) (.app (tv 1) (tv 0)) (tapps (Templates.interpTm l) [tv 4, tv 3, tv 2, tv 1])))

/-! ### Sizes

A size is `∞`, or a size variable (any neutral) plus a number of `↑`s. -/

/-- `(base, k)` for `↑ᵏ base`; `none` as the base means `∞`. -/
partial def sizeView : Val R → Option (Val R) × Nat
  | .szInf => (none, 0)
  | .szSuc s => let (b, k) := sizeView s; (b, k + 1)
  | v => (some v, 0)

private def sameBase : Val R → Val R → Bool
  | .neutral (.local a) #[], .neutral (.local b) #[] => a == b
  | .neutral (.mvar a) #[], .neutral (.mvar b) #[] => a == b
  | _, _ => false

def sizeEq (a b : Val R) : Bool :=
  match sizeView a, sizeView b with
  | (none, _), (none, _) => true
  | (some x, k), (some y, m) => k == m && sameBase x y
  | _, _ => false

/-- `a ≤ b` for sizes: anything is below `∞`; `↑ᵏ x ≤ ↑ᵐ x` when `k ≤ m`; and a
variable `x : Size< u` (from `tys`) satisfies `↑ᵏ x ≤ b` when `↑ᵏ⁻¹ u ≤ b`
(`x < u`, so `x + 1 ≤ u`), or when `u ≤ b` for `k = 0`. -/
partial def sizeLe (tys : Array (VTy R)) (a b : Val R) : Bool :=
  match sizeView a, sizeView b with
  | _, (none, _) => true
  | (none, _), (some _, _) => false
  | (some x, k), (some y, m) =>
    (k ≤ m && sameBase x y) ||
    match x with
    | .neutral (.local lx) #[] => match tys[lx]? with
      | some (.sizeLt u) => sizeLe tys ((List.range (k - 1)).foldl (fun s _ => .szSuc s) u) b
      | _ => false
    | _ => false

/-- The predecessor of a size, for `con`/`cocon`/`out`: `↑s ↦ s`, `∞ ↦ ∞`; `none`
for a size variable, which can't be built from or observed. -/
def sizePred? : Val R → Option (Val R)
  | .szInf => some .szInf
  | .szSuc s => some s
  | _ => none

/-- `f : (s : Size) → ((j : Size< s) → (i : I) → (y : μ^j D i) → P i y) → (i : I) → (x : μ^s D i) → P i x` -/
def sfixFunTy (g : Globals R) (l : Level) (I D P : Val R) (w : R) : VTy R :=
  let pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit w) a b
  -- s0 P1 D2 I3 ; j0 s1 P2 D3 I4 ; i0 j1 s2 P3 D4 I5 ; y0 i1 j2 s3 P4
  -- rec0 s1 P2 D3 I4 ; i0 rec1 s2 P3 D4 I5 ; x0 i1 rec2 s3 P4
  eval g [P, D, I] (.pi "s" .default (.qlit 0) .size
    (pi "rec" (.pi "j" .default (.qlit 0) (.sizeLt (tv 0))
        (pi "i" (tv 4) (pi "y" (.mu l (tv 5) (tv 4) (tv 0) (tv 1) none) (tapps (tv 4) [tv 1, tv 0]))))
      (pi "i" (tv 4) (pi "x" (.mu l (tv 5) (tv 4) (tv 0) (tv 2) none) (tapps (tv 4) [tv 1, tv 0])))))

/-- `m : (0 j : Size< s) → (0 i : I) → (xs : ⟦D⟧ (μ^j D) i) → P i (con xs)` -/
def scaseMethodTy (g : Globals R) (l : Level) (I D P s : Val R) (w : R) : VTy R :=
  -- j0 s1 P2 D3 I4 ; i0 j1 s2 P3 D4 I5 ; xs0 i1 j2 s3 P4 D5 I6
  eval g [s, P, D, I] (.pi "j" .default (.qlit 0) (.sizeLt (tv 0)) (.pi "i" .default (.qlit 0) (tv 4)
    (.pi "xs" .default (.qlit w)
      (tapps (Templates.interpTm l) [tv 5, tv 4, .lam "j'" (.mu l (tv 6) (tv 5) (tv 0) (tv 2) none), tv 0])
      (tapps (tv 4) [tv 1, .con (tv 0)]))))

/-- `f : (s : Size) → ((i : I) → A i → ν^s D i) → (i : I) → A i → ν^{↑s} D i` -/
def scofixFunTy (g : Globals R) (l : Level) (I D A : Val R) (w : R) : VTy R :=
  let pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit w) a b
  -- s0 A1 D2 I3 ; i0 s1 A2 D3 I4 ; a0 i1 s2 A3 D4 I5 ; rec0 s1 A2 D3 I4 ; i0 rec1 s2 A3 D4 I5 ; a0 i1 rec2 s3 A4 D5 I6
  eval g [A, D, I] (.pi "s" .default (.qlit 0) .size
    (pi "rec" (pi "i" (tv 3) (pi "a" (.app (tv 2) (tv 0)) (.nu l (tv 5) (tv 4) (tv 1) (tv 2) none)))
      (pi "i" (tv 4) (pi "a" (.app (tv 3) (tv 0)) (.nu l (tv 6) (tv 5) (tv 1) (.szSuc (tv 3)) none)))))

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
      | .ecase z m env bs, _ => ty := Closure.inst g m acc; acc := vEcase g z m acc env bs
      | .delim v P a b c, _ => ty := vApp g P acc; acc := vDelim g v P a b c acc
      | .ind l I D v P m i, _ => ty := vApp g (vApp g P i) acc; acc := vInd g l I D v P m i acc
      | .out, .nu l I D i s _ =>
        ty := vInterp g l I D (nuFamilyAt l I D ((sizePred? s).getD .szInf)) i; acc := vOut g acc
      | .sfix l I D v P f s i, _ => ty := vApp g (vApp g P i) acc; acc := vSfix g l I D v P f s i acc
      | .scase l I D v P m s i, _ => ty := vApp g (vApp g P i) acc; acc := vScase g l I D v P m s i acc
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
  | .qty | .enum _ | .size | .sizeLt _ => some 1
  | .desc l _ => some (.succ (.succ l))
  | .mu l .. | .nu l .. => some (.succ l)
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

/-- **Subtyping** (stage 4f): `A ≤ B`. Sized inductive types are covariant in their size
(`μ^s ≤ μ^t` when `s ≤ t`), coinductive ones contravariant, functions contravariant in
the domain, and everything else is conversion. -/
partial def subTy (g : Globals R) (tys : Array (VTy R)) (A B : VTy R) : Bool :=
  let v := Val.var tys.size
  match A, B with
  | .mu l I D i s _, .mu l' I' D' i' s' _ =>
    l.equiv l' && sizeLe tys s s' && convTy g tys I I' && conv g tys (.desc l I) D D' && conv g tys I i i'
  | .nu l I D i s _, .nu l' I' D' i' s' _ =>
    l.equiv l' && sizeLe tys s' s && convTy g tys I I' && conv g tys (.desc l I) D D' && conv g tys I i i'
  | .pi _ _ q A₁ B₁, .pi _ _ q' A₂ B₂ =>
    (conv g tys .qty q q' || isProp g tys A) && subTy g tys A₂ A₁ &&
      subTy g (tys.push A₂) (Closure.inst g B₁ v) (Closure.inst g B₂ v)
  | .sigma _ q A₁ B₁, .sigma _ q' A₂ B₂ =>
    conv g tys .qty q q' && subTy g tys A₁ A₂ &&
      subTy g (tys.push A₁) (Closure.inst g B₁ v) (Closure.inst g B₂ v)
  | .sizeLt _, .size => true
  | .sizeLt s, .sizeLt t => sizeLe tys s t
  | _, _ => convTy g tys A B

end Wiz
