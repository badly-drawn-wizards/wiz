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
    (.pi "_" .default (.qlit w) (.mu l (tv 2) (tv 1) (tv 0) none) (.sort v)))

/-- `m : (0 i : I) → (xs : ⟦D⟧ (μ D) i) → (ih : All D (μ D) P i xs) → P i (con xs)` -/
def indMethodTy (g : Globals R) (l v : Level) (I D P : Val R) (w : R) : VTy R :=
  -- i0 P1 D2 I3 ; xs0 i1 P2 D3 I4 ; ih0 xs1 i2 P3 D4 I5
  let X₁ : Term R := .lam "j" (.mu l (tv 4) (tv 3) (tv 0) none)
  let X₂ : Term R := .lam "j" (.mu l (tv 5) (tv 4) (tv 0) none)
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
      | .out, .nu l I D i _ => ty := vInterp g l I D (nuFamily l I D) i; acc := vOut g acc
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
  | .qty | .enum _ => some 1
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
  --<sol
  if isProp g tys ty then true else
  let a := unCast a
  let b := unCast b
  match ty with
  | .pi _ _ _ dom cod =>
    let v := Val.var tys.size
    conv g (tys.push dom) (Closure.inst g cod v) (vApp g a v) (vApp g b v)
  | .sigma _ _ A B =>
    let a₁ := vFst a
    conv g tys A a₁ (vFst b) && conv g tys (Closure.inst g B a₁) (vSnd a) (vSnd b)
  | .unit _ => true
  | .qty => match sameQty a b with
    | some r => r
    | none => (convNe g tys a b).isSome
  | .enum _ => match a, b with
    | .tag _ i, .tag _ j => i == j
    | _, _ => (convNe g tys a b).isSome
  | .desc l I => match a, b with
    | .dret i, .dret j => conv g tys I i j
    | .darg q S E, .darg q' S' E' =>
      conv g tys .qty q q' && convTy g tys S S' &&
        conv g tys (.pi "s" .default (.qlit 1) S (.mk [I] (.desc l (.var 1)))) E E'
    | .drec q j E, .drec q' j' E' =>
      conv g tys .qty q q' && conv g tys I j j' && conv g tys (.desc l I) E E'
    | _, _ => (convNe g tys a b).isSome
  | .mu l I D i _ => match a, b with
    | .con x, .con y => conv g tys (vInterp g l I D (muFamily l I D) i) x y
    | _, _ => (convNe g tys a b).isSome
  | .nu l I D i _ => match a, b with
    | .coit _ _ _ S st j s, .coit _ _ _ S' st' j' s' =>
      conv g tys (coitStateTy l I 1) S S' && conv g tys (coitStepTy g l I D S 1) st st' &&
        conv g tys I j j' && conv g tys (vApp g S j) s s'
    | _, _ => (convNe g tys a b).isSome
  | .sort _ => convTy g tys a b
  | _ => (convNe g tys a b).isSome
where
  unCast (v : Val R) : Val R :=
    match v with
    | .neutral (.cast A B _ t) #[] => if convTy g tys A B then unCast t else v
    | v => v
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let v := Val.var tys.size
  match a, b with
  | .sort u, .sort u' => u.equiv u'
  | .pi _ _ q A B, .pi _ _ q' A' B' =>
    (convQty q q' || isProp g tys a) && convTy g tys A A' &&
      convTy g (tys.push A) (Closure.inst g B v) (Closure.inst g B' v)
  | .sigma _ q A B, .sigma _ q' A' B' =>
    (convQty q q' || isProp g tys a) && convTy g tys A A' &&
      convTy g (tys.push A) (Closure.inst g B v) (Closure.inst g B' v)
  | .qty, .qty => true
  | .enum ls, .enum ls' => ls.length == ls'.length
  | .desc l I, .desc l' I' => l.equiv l' && convTy g tys I I'
  | .mu l I D i _, .mu l' I' D' i' _ | .nu l I D i _, .nu l' I' D' i' _ =>
    l.equiv l' && convTy g tys I I' && conv g tys (.desc l I) D D' && conv g tys I i i'
  | .unit u, .unit u' => u.equiv u'
  | .empty u, .empty u' => u.equiv u'
  | .neutral .., .neutral .. => (convNe g tys a b).isSome
  | _, _ => false
where
  convQty (q q' : Val R) : Bool := conv g tys .qty q q'
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let .neutral h sp := a | none
  let .neutral h' sp' := b | none
  unless sp.size == sp'.size do none
  let isProof : Head R → Bool
    | .refl .. | .reflTy _ | .transp .. => true
    | _ => false
  let headsEq := match h, h' with
    | .eq A x y, .eq A' x' y' => convTy g tys A A' && conv g tys A x x' && conv g tys A y y'
    | .eqTy A B, .eqTy A' B' => convTy g tys A A' && convTy g tys B B'
    | .cast A B _ t, .cast A' B' _ t' => convTy g tys A A' && convTy g tys B B' && conv g tys A t t'
    | _, _ => (isProof h && isProof h') || h.equiv h'
  unless headsEq do none
  let mut ty ← headType g tys h
  let mut acc : Val R := .neutral h #[]
  for e in sp, e' in sp' do
    match e, e', ty with
    | .app x, .app y, .pi _ _ _ dom cod =>
      unless conv g tys dom x y do none
      ty := Closure.inst g cod x
      acc := vApp g acc x
    | .fst, .fst, .sigma _ _ A _ =>
      ty := A
      acc := vFst acc
    | .snd, .snd, .sigma _ _ _ B =>
      ty := Closure.inst g B (vFst acc)
      acc := vSnd acc
    | .split q _ m _ _ body, .split q' _ m' _ _ body', sty@(.sigma _ _ A B) =>
      unless conv g tys .qty q q' do none
      let l := tys.size
      unless convTy g (tys.push sty) (Closure.inst g m (Val.var l)) (Closure.inst g m' (Val.var l)) do none
      let x : Val R := Val.var l
      let y : Val R := Val.var (l + 1)
      let bodyTy := Closure.inst g m (.pair x y)
      let tys₂ := (tys.push A).push (Closure.inst g B x)
      unless conv g tys₂ bodyTy (Closure.inst2 g body x y) (Closure.inst2 g body' x y) do none
      ty := Closure.inst g m acc
      acc := vSplit g q acc "z" m "x" "y" body
    | .absurd m, .absurd m', _ =>
      unless convTy g tys m m' do none
      ty := m
      acc := vAbsurd m acc
    | .ecase z m env bs, .ecase _ m' env' bs', ety@(.enum ls) =>
      let l := tys.size
      unless convTy g (tys.push ety) (Closure.inst g m (Val.var l)) (Closure.inst g m' (Val.var l)) do none
      unless bs.length == bs'.length do none
      for b in bs, b' in bs', k in [0:bs.length] do
        unless conv g tys (Closure.inst g m (.tag ls k)) (eval g env b) (eval g env' b') do none
      ty := Closure.inst g m acc
      acc := vEcase g z m acc env bs
    | .delim v P a b c, .delim v' P' a' b' c', .desc l I =>
      unless v.equiv v' && conv g tys (delimMotiveTy l v I 1) P P' do none
      let (ta, tb, tc) := delimMethodTys g l I P 1
      unless conv g tys ta a a' && conv g tys tb b b' && conv g tys tc c c' do none
      ty := vApp g P acc
      acc := vDelim g v P a b c acc
    | .ind l I D v P m i, .ind _ _ _ v' P' m' i', _ =>
      unless v.equiv v' && conv g tys (indMotiveTy g l v I D 1) P P' do none
      unless conv g tys (indMethodTy g l v I D P 1) m m' && conv g tys I i i' do none
      ty := vApp g (vApp g P i) acc
      acc := vInd g l I D v P m i acc
    | .out, .out, .nu l I D i _ =>
      ty := vInterp g l I D (nuFamily l I D) i
      acc := vOut g acc
    | _, _, _ => none
  pure ty
  --|ex
  --| sorry
  --sol>

end

end Wiz
