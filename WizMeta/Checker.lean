import WizMeta.Syntax
import WizMeta.Templates

/-!
# The reference checker

Written from the rules of `WizMeta/Spec/`, to be read next to them. It is meant to be
obviously right, not fast:

* **substitution-based**: no environments, no closures, no values. A redex is contracted
  by substituting into the term;
* **typed weak-head reduction**: `whnf` takes the context. Where a rule depends on
  whether a type is a proposition, the type's sort is *computed* (`sortOf`), so there is
  no "unknown" for a type whose sort is closed;
* **no proof is reduced**: `whnf` is only ever called on types and on terms of a type
  that is not a proposition (conversion answers `true` at a proposition before looking at
  the terms), and it never looks at the proof arguments of `cast`, `transp`, `absurd`;
  `let` and application substitute their argument unevaluated;
* **no syntactic side conditions**: every side condition is a level condition, a
  comparison of quantity labels or tag numbers, or a call of conversion. In particular
  regularity at inert types (T1) is decided by `convTy` on the two types of a stuck cast;
* **no quotation**: there are no values to read back;
* **fuel**: every function is structurally recursive on its fuel, so everything here is
  total, and a result is `ok`, a rejection, or `Err.fuel` (which is neither).

Nothing is proved about it yet (metatheory-plan M2 is soundness against the spec).

Not implemented (the term is rejected, or the redex stays stuck): usage checking (quantities
are labels), sizes, `ν`, `split`, numerals, and the rules of PR #40 (type equations
between `μ` types and casts at `μ`/`Desc` by codes: both stay stuck here).
-/

namespace WizMeta

inductive Err where
  /-- the fuel ran out: not a verdict -/
  | fuel
  /-- the term is rejected -/
  | fail (msg : String)
  deriving Repr, Inhabited

instance : ToString Err := ⟨fun | .fuel => "out of fuel" | .fail m => m⟩

/-- Which variant of the rules to check. The defaults are the spec's (T1 and up). -/
structure Opts where
  /-- accept a `Π`/`Σ` without a sort (the spec does not: mandatory sorts). The rules never
  read the annotation except to verify it, so this only skips that verification. -/
  sortsOptional : Bool := false
  /-- form `a =_A b`, `refl`, `transp` only at a sort that is never `Prop` (the kernels'
  rule). The spec forms them at any sort, where `a =_A b ⟶ True` at a proposition `A`:
  the kernels' own reducts contain such equations. -/
  eqNeverZero : Bool := false
  /-- regularity at inert types as a conversion rule (T1). Off: T0. -/
  inertReg : Bool := true
  deriving Repr, Inhabited

structure Env where
  sig : Sig := []
  opts : Opts := {}

abbrev M := Except Err

def fail {α : Type} (msg : String) : M α := throw (.fail msg)

namespace Tm

def True' : Tm := .unit 0
def False' : Tm := .empty 0

/-- `(a → b) × (b → a)`: what an equation between two propositions means. -/
def iff (a b : Tm) : Tm :=
  .sigma .zero (some 0) (.pi .zero (some 0) a b.shift) (.pi .zero (some 0) b.shift (a.shiftN 2))

/-- The canonical type formers: two different ones are never equal. -/
def canonical : Tm → Bool
  | .pi .. | .sigma .. | .sort _ | .unit _ | .empty _ | .enum _ | .ulift .. | .desc .. | .mu .. => true
  | _ => false

end Tm

/-- `Sort u ≡ Sort w` and the like: `True` for equal levels, `False` for two different
closed levels, stuck otherwise (the answer must survive a level substitution). -/
def eqLevels (u w : Lvl) (stuck : Tm) : Tm :=
  if u.equiv w then Tm.True'
  else if u.toNat?.isSome && w.toNat?.isSome then Tm.False'
  else stuck

open Tm in
mutual

/-- Weak-head normal form of a type, or of a term whose type is not a proposition. -/
def whnf (E : Env) : Nat → Ctx → Tm → M Tm
  | 0, _, _ => throw .fuel
  | n + 1, Γ, t =>
    match t with
    -- δ
    | .const c us =>
      match E.sig.find? c with
      | some d =>
        match d.value with
        | some v => whnf E n Γ (v.instL us)
        | none => pure t
      | none => pure t
    -- β
    | .app f a => do
      let f' ← whnf E n Γ f
      match f' with
      | .lam b => whnf E n Γ (b.inst a)
      | _ => pure (.app f' a)
    -- ζ
    | .letE _ _ v b => whnf E n Γ (b.inst v)
    | .ann t _ => whnf E n Γ t
    | .fst p => do
      let p' ← whnf E n Γ p
      match p' with
      | .pair a _ => whnf E n Γ a
      | _ => pure (.fst p')
    | .snd p => do
      let p' ← whnf E n Γ p
      match p' with
      | .pair _ b => whnf E n Γ b
      | _ => pure (.snd p')
    | .ecase mot s bs => do
      let s' ← whnf E n Γ s
      match s' with
      | .tag _ i =>
        match bs.branch? i with
        | some b => whnf E n Γ b
        | none => pure (.ecase mot s' bs)
      | _ => pure (.ecase mot s' bs)
    | .down t => do
      let t' ← whnf E n Γ t
      match t' with
      | .up a => whnf E n Γ a
      | _ => pure (.down t')
    | .eq A a b => whnfEq E n Γ A a b
    | .eqTy A B => whnfEqTy E n Γ A B
    | .cast A B e t => whnfCast E n Γ A B e t
    -- ⟦D⟧ X i, by the description
    | .interp l I D X i => do
      let D' ← whnf E n Γ D
      let l1 := l.succ
      let rest (D₁ : Tm) : Tm := .interp l I.shift D₁ X.shift i.shift
      match D' with
      | .dret j => pure (.sigma .zero (some l1) (.eq I j i) (.unit l1))
      | .darg q S D₁ =>
        match ← whnf E n Γ q with
        | .qlit q => pure (.sigma q (some l1) S (rest (.app D₁.shift (.var 0))))
        | q' => pure (.interp l I (.darg q' S D₁) X i)
      | .drec q j D₁ =>
        match ← whnf E n Γ q with
        | .qlit q => pure (.sigma q (some l1) (.app X j) (rest D₁.shift))
        | q' => pure (.interp l I (.drec q' j D₁) X i)
      | .dhrec q H j D₁ =>
        match ← whnf E n Γ q with
        | .qlit q =>
          pure (.sigma q (some l1) (.pi .many (some l1) H (.app X.shift (.app j.shift (.var 0)))) (rest D₁.shift))
        | q' => pure (.interp l I (.dhrec q' H j D₁) X i)
      | _ => pure (.interp l I D' X i)
    | .delim v P mret marg mrec mhrec D => do
      let D' ← whnf E n Γ D
      let again (D₁ : Tm) : Tm := .delim v P mret marg mrec mhrec D₁
      match D' with
      | .dret i => whnf E n Γ (.app mret i)
      | .darg q S D₁ =>
        whnf E n Γ (apps marg [q, S, D₁,
          .lam (.delim v P.shift mret.shift marg.shift mrec.shift mhrec.shift (.app D₁.shift (.var 0)))])
      | .drec q j D₁ => whnf E n Γ (apps mrec [q, j, D₁, again D₁])
      | .dhrec q H j D₁ => whnf E n Γ (apps mhrec [q, H, j, D₁, again D₁])
      | _ => pure (again D')
    | .ind l I D v P m i x => do
      let x' ← whnf E n Γ x
      match x' with
      | .con xs => whnf E n Γ (apps m [i, xs, indHyps l v I D P m i xs])
      | _ => pure (.ind l I D v P m i x')
    | _ => pure t

/-- `a =_A b`, by the weak-head normal form of `A`. -/
def whnfEq (E : Env) : Nat → Ctx → Tm → Tm → Tm → M Tm
  | 0, _, _, _, _ => throw .fuel
  | n + 1, Γ, A, a, b => do
    let A' ← whnf E n Γ A
    let stuck : Tm := .eq A' a b
    match ← propOf E n Γ A' with
    | some true => pure True'
    | none => pure stuck
    | some false =>
      match A' with
      | .pi _ _ A₁ B =>
        -- funext: (0 x : A₁) → a x =_{B x} b x
        pure (.pi .zero (some 0) A₁ (.eq B (.app a.shift (.var 0)) (.app b.shift (.var 0))))
      | .sigma _ _ A₁ B =>
        -- (0 e : a.1 =_{A₁} b.1) × (cast (B a.1) (B b.1) ê a.2 =_{B b.1} b.2)
        -- ê = transp A₁ a.1 (λy _. B a.1 ≡ B y) (reflTy (B a.1)) b.1 e
        let a1 : Tm := .fst a
        let b1 : Tm := .fst b
        let Ba := B.inst a1
        let Bb := B.inst b1
        -- under y, _ : `B y` is `B` with its variable replaced by `y` (index 1)
        let By := (B.ren (upRen (· + 2))).inst (.var 1)
        let P : Tm := .lam (.lam (.eqTy (Ba.shiftN 2) By))
        let ê : Tm := .transp A₁.shift a1.shift P.shift (.reflTy Ba.shift) b1.shift (.var 0)
        pure (.sigma .zero (some 0) (.eq A₁ a1 b1)
          (.eq Bb.shift (.cast Ba.shift Bb.shift ê (Tm.snd a).shift) (Tm.snd b).shift))
      | .unit _ => pure True'
      | .empty _ => pure True'
      | .enum _ => do
        let a' ← whnf E n Γ a
        let b' ← whnf E n Γ b
        match a', b' with
        | .tag _ i, .tag _ j => pure (if i == j then True' else False')
        | _, _ => pure (.eq A' a' b')
      | .sort l =>
        -- propext at `Prop`; type equality above it
        if l.isZero then pure (iff a b)
        else if l.neverZero then whnfEqTy E n Γ a b
        else pure stuck
      | .ulift _ A₀ => do
        -- a lifted proposition has one inhabitant; otherwise compare the contents
        let A₀' ← whnf E n Γ A₀
        match ← propOf E n Γ A₀' with
        | some true => pure True'
        | some false => whnfEq E n Γ A₀' (.down a) (.down b)
        | none => pure stuck
      | .mu l I D i => do
        -- two constructors: by the description
        let a' ← whnf E n Γ a
        let b' ← whnf E n Γ b
        match a', b' with
        | .con x, .con y =>
          match ← eqPayload E n Γ l I (muFamily l I D) i D x y with
          | some r => whnf E n Γ r
          | none => pure (.eq A' a' b')
        | _, _ => pure (.eq A' a' b')
      | _ => pure stuck

/-- `x = y` for two payloads at `⟦D⟧ X i`, by the description; `none` when a tag is not
canonical (then the whole equation is stuck). -/
def eqPayload (E : Env) : Nat → Ctx → Lvl → Tm → Tm → Tm → Tm → Tm → Tm → M (Option Tm)
  | 0, _, _, _, _, _, _, _, _ => throw .fuel
  | n + 1, Γ, l, I, X, i, D, x, y => do
    let D' ← whnf E n Γ D
    -- a field's equation, and the rest's unless the rest is just `ret`
    let withRest (A D₁ r : Tm) : M Tm := do
      match ← whnf E n Γ D₁ with
      | .dret _ => pure A
      | _ => pure (.sigma .zero (some 0) A r.shift)
    match D' with
    | .dret _ => pure (some True')
    | .darg _ S D₁ =>
      match ← tagField E n Γ S with
      | some (k, lifted) => do
        let tagOf (p : Tm) : Tm := if lifted then .down (.fst p) else .fst p
        match ← whnf E n Γ (tagOf x), ← whnf E n Γ (tagOf y) with
        | .tag _ a, .tag _ b =>
          if a == b then
            let t : Tm := if lifted then .up (.tag k a) else .tag k a
            eqPayload E n Γ l I X i (.app D₁ t) (.snd x) (.snd y)
          else pure (some (.eq (.interp l I D' X i) x y))
        | _, _ => pure none
      | none => pure (some (.eq (.interp l I D' X i) x y))
    | .drec _ j D₁ => do
      let some r ← eqPayload E n Γ l I X i D₁ (.snd x) (.snd y) | pure none
      pure (some (← withRest (.eq (.app X j) (.fst x) (.fst y)) D₁ r))
    | .dhrec _ H j D₁ => do
      let some r ← eqPayload E n Γ l I X i D₁ (.snd x) (.snd y) | pure none
      let F : Tm := .pi .many (some l.succ) H (.app X.shift (.app j.shift (.var 0)))
      pure (some (← withRest (.eq F (.fst x) (.fst y)) D₁ r))
    | _ => pure none

/-- Is this field type an enumeration of constructor tags, possibly lifted? -/
def tagField (E : Env) : Nat → Ctx → Tm → M (Option (Nat × Bool))
  | 0, _, _ => throw .fuel
  | n + 1, Γ, S => do
    match ← whnf E n Γ S with
    | .enum k => pure (some (k, false))
    | .ulift _ A =>
      match ← whnf E n Γ A with
      | .enum k => pure (some (k, true))
      | _ => pure none
    | _ => pure none

/-- `A ≡ B` for two types: propositions are equal when equivalent, other types by their
formers. -/
def whnfEqTy (E : Env) : Nat → Ctx → Tm → Tm → M Tm
  | 0, _, _, _ => throw .fuel
  | n + 1, Γ, A, B => do
    let A' ← whnf E n Γ A
    let B' ← whnf E n Γ B
    let stuck : Tm := .eqTy A' B'
    let pa ← propOf E n Γ A'
    let pb ← propOf E n Γ B'
    match pa, pb with
    | some true, some true => pure (iff A' B')
    | none, _ => pure stuck
    | _, none => pure stuck
    | some true, some false => pure False'
    | some false, some true => pure False'
    | some false, some false =>
      match A', B' with
      | .pi q _ A₁ B₁, .pi q' _ A₂ B₂ =>
        if q != q' then pure False' else
        -- (0 e : A₂ ≡ A₁) × ((0 x : A₂) → B₁ (cast A₂ A₁ e x) ≡ B₂ x)
        let c : Tm := .cast (A₂.shiftN 2) (A₁.shiftN 2) (.var 1) (.var 0)
        pure (.sigma .zero (some 0) (.eqTy A₂ A₁)
          (.pi .zero (some 0) A₂.shift
            (.eqTy ((B₁.ren (upRen (· + 2))).inst c) (B₂.ren (upRen (· + 1))))))
      | .sigma q _ A₁ B₁, .sigma q' _ A₂ B₂ =>
        if q != q' then pure False' else
        -- (0 e : A₁ ≡ A₂) × ((0 x : A₁) → B₁ x ≡ B₂ (cast A₁ A₂ e x))
        let c : Tm := .cast (A₁.shiftN 2) (A₂.shiftN 2) (.var 1) (.var 0)
        pure (.sigma .zero (some 0) (.eqTy A₁ A₂)
          (.pi .zero (some 0) A₁.shift
            (.eqTy (B₁.ren (upRen (· + 1))) ((B₂.ren (upRen (· + 2))).inst c))))
      | .sort u, .sort w => pure (eqLevels u w stuck)
      | .unit u, .unit w => pure (eqLevels u w stuck)
      | .empty u, .empty w => pure (eqLevels u w stuck)
      | .enum k, .enum k' => pure (if k == k' then True' else False')
      | .ulift u A₀, .ulift w B₀ =>
        if u.equiv w then whnfEqTy E n Γ A₀ B₀
        else if u.toNat?.isSome && w.toNat?.isSome then pure False'
        else pure stuck
      | .desc l I, .desc l' I' =>
        if l.equiv l' then whnfEqTy E n Γ I I' else pure stuck
      -- (by codes, as in PR #40: not implemented)
      | .mu .., .mu .. => pure stuck
      | _, _ => pure (if A'.canonical && B'.canonical then False' else stuck)

/-- `cast A B e t`, by the weak-head normal forms of `A` and `B`. The proof `e` is only
ever projected, never looked at. -/
def whnfCast (E : Env) : Nat → Ctx → Tm → Tm → Tm → Tm → M Tm
  | 0, _, _, _, _, _ => throw .fuel
  | n + 1, Γ, A, B, e, t => do
    let A' ← whnf E n Γ A
    let B' ← whnf E n Γ B
    let stuck : Tm := .cast A' B' e t
    let pa ← propOf E n Γ A'
    let pb ← propOf E n Γ B'
    -- a cast between propositions is a proof; and the structural rules use the parts of
    -- `e`, which exist when `A ≡ B` computes by formers: both not propositions
    if !(pa == some false && pb == some false) then pure stuck else
    match A', B' with
    | .pi q _ A₁ B₁, .pi q' _ A₂ B₂ =>
      if q != q' then pure stuck else
      -- λx. cast (B₁ x̂) (B₂ x) (e.2 x) (t x̂),  x̂ = cast A₂ A₁ e.1 x
      let x' : Tm := .cast A₂.shift A₁.shift (.fst e.shift) (.var 0)
      pure (.lam (.cast ((B₁.ren (upRen (· + 1))).inst x') B₂ (.app (.snd e.shift) (.var 0)) (.app t.shift x')))
    | .sigma q _ A₁ B₁, .sigma q' _ A₂ B₂ =>
      if q != q' then pure stuck else
      -- (c₁, cast (B₁ t.1) (B₂ c₁) (e.2 t.1) t.2),  c₁ = cast A₁ A₂ e.1 t.1
      let t1 : Tm := .fst t
      let c1 : Tm := .cast A₁ A₂ (.fst e) t1
      pure (.pair c1 (.cast (B₁.inst t1) (B₂.inst c1) (.app (.snd e) t1) (.snd t)))
    | .sort u, .sort w => if u.equiv w then whnf E n Γ t else pure stuck
    | .empty u, .empty w => if u.equiv w then whnf E n Γ t else pure stuck
    | .unit u, .unit w => if u.equiv w then pure .tt else pure stuck
    | .enum k, .enum k' => if k == k' then whnf E n Γ t else pure stuck
    | .ulift u A₀, .ulift w B₀ =>
      if u.equiv w then pure (.up (.cast A₀ B₀ e (.down t))) else pure stuck
    | _, _ => pure stuck

/-- Is this type (in weak-head normal form) a proposition? `none` only when its sort
depends on a level parameter. -/
def propOf (E : Env) : Nat → Ctx → Tm → M (Option Bool)
  | 0, _, _ => throw .fuel
  | n + 1, Γ, A => do
    let s ← sortOf E n Γ A
    pure (if s.isZero then some true else if s.neverZero then some false else none)

/-- The sort of a well-formed type in weak-head normal form. -/
def sortOf (E : Env) : Nat → Ctx → Tm → M Lvl
  | 0, _, _ => throw .fuel
  | n + 1, Γ, A =>
    match A with
    | .sort l => pure l.succ
    | .pi _ (some s) _ _ => pure s
    | .sigma _ (some s) _ _ => pure s
    | .pi _ none A₁ B => do
      let i ← sortOfTy E n Γ A₁
      let j ← sortOfTy E n (A₁ :: Γ) B
      pure (.imax i j)
    | .sigma _ none A₁ B => do
      let i ← sortOfTy E n Γ A₁
      let j ← sortOfTy E n (A₁ :: Γ) B
      pure (.max i j)
    | .unit l => pure l
    | .empty l => pure l
    | .ulift l _ => pure l
    | .enum _ => pure 1
    | .qty => pure 1
    | .eq .. => pure 0
    | .eqTy .. => pure 0
    | .desc l _ => pure l.succ.succ
    | .mu l _ _ _ => pure l.succ
    | .interp l _ _ _ _ => pure l.succ
    | _ => do
      let T ← typeOfNe E n Γ A
      match ← whnf E n Γ T with
      | .sort l => pure l
      | _ => fail "sortOf: not a type"

def sortOfTy (E : Env) : Nat → Ctx → Tm → M Lvl
  | 0, _, _ => throw .fuel
  | n + 1, Γ, A => do sortOf E n Γ (← whnf E n Γ A)

/-- The type of a well-typed neutral term, without re-checking it. -/
def typeOfNe (E : Env) : Nat → Ctx → Tm → M Tm
  | 0, _, _ => throw .fuel
  | n + 1, Γ, t =>
    match t with
    | .var i =>
      match Γ.lookup i with
      | some T => pure T
      | none => fail s!"variable {i} out of scope"
    | .const c us =>
      match E.sig.find? c with
      | some d => pure (d.type.instL us)
      | none => fail s!"unknown constant {c}"
    | .app f a => do
      match ← whnfS E n Γ (← typeOfNe E n Γ f) with
      | .pi _ _ _ B => pure (B.inst a)
      | _ => fail "typeOfNe: not a function"
    | .fst p => do
      match ← whnfS E n Γ (← typeOfNe E n Γ p) with
      | .sigma _ _ A _ => pure A
      | _ => fail "typeOfNe: not a pair"
    | .snd p => do
      match ← whnfS E n Γ (← typeOfNe E n Γ p) with
      | .sigma _ _ _ B => pure (B.inst (.fst p))
      | _ => fail "typeOfNe: not a pair"
    | .down p => do
      match ← whnfS E n Γ (← typeOfNe E n Γ p) with
      | .ulift _ A => pure A
      | _ => fail "typeOfNe: not a lift"
    | .absurd mot _ => pure mot
    | .ecase mot s _ => pure (mot.inst s)
    | .cast _ B _ _ => pure B
    | .transp _ _ P _ b e => pure (.app (.app P b) e)
    | .refl A a => pure (.eq A a a)
    | .reflTy A => pure (.eqTy A A)
    | .ann _ A => pure A
    | .delim _ P _ _ _ _ D => pure (.app P D)
    | .ind _ _ _ _ P _ i x => pure (apps P [i, x])
    | .interp l _ _ _ _ => pure (.sort l.succ)
    | _ => fail "typeOfNe: not a neutral term"

/-- Weak-head normal form up to regularity at inert types (T1): a stuck cast at the head
whose two types are convertible, one of them inert, is removed. -/
def whnfS (E : Env) : Nat → Ctx → Tm → M Tm
  | 0, _, _ => throw .fuel
  | n + 1, Γ, t => do
    let t' ← whnf E n Γ t
    if !E.opts.inertReg then pure t' else
    match ← strip E n Γ t' with
    | some u => whnfS E n Γ u
    | none => pure t'

/-- Remove the stuck cast at the head of a neutral term, if InReg_conv applies to it. -/
def strip (E : Env) : Nat → Ctx → Tm → M (Option Tm)
  | 0, _, _ => throw .fuel
  | n + 1, Γ, t =>
    match t with
    | .cast A B _ u => do
      if ← inert E n Γ A then
        if ← convTy E n Γ A B then pure (some u) else pure none
      else pure none
    | .app f a => do pure ((← strip E n Γ f).map (.app · a))
    | .fst p => do pure ((← strip E n Γ p).map .fst)
    | .snd p => do pure ((← strip E n Γ p).map .snd)
    | .down p => do pure ((← strip E n Γ p).map .down)
    | .ecase mot s bs => do pure ((← strip E n Γ s).map (.ecase mot · bs))
    | .delim v P a b c h D => do pure ((← strip E n Γ D).map (.delim v P a b c h ·))
    | .ind l I D v P m i x => do pure ((← strip E n Γ x).map (.ind l I D v P m i ·))
    | .interp l I D X i => do pure ((← strip E n Γ D).map (.interp l I · X i))
    | _ => pure none

/-- An inert type: first-order data. `Enum`, `Unit` above `Prop`, lifts and `Σ`s of inert
types that are not propositions. (With `μ`: data whose fields are inert; not implemented.) -/
def inert (E : Env) : Nat → Ctx → Tm → M Bool
  | 0, _, _ => throw .fuel
  | n + 1, Γ, A => do
    let A' ← whnf E n Γ A
    match A' with
    | .enum _ => pure true
    | .unit l => pure l.neverZero
    | .ulift l A₀ => if l.neverZero then inert E n Γ A₀ else pure false
    | .sigma _ _ A₁ B => do
      if !(← sortOf E n Γ A').neverZero then pure false
      else if !(← inert E n Γ A₁) then pure false
      else inert E n (A₁ :: Γ) B
    | .mu l I D _ => do
      if ← inert E n Γ I then inertDesc E n Γ l I D else pure false
    | _ => pure false

/-- Every field of the description is inert: `ret`, `rec`, and `arg` at inert types (a
tag field is walked tag by tag, any other under a variable). No `hrec`. -/
def inertDesc (E : Env) : Nat → Ctx → Lvl → Tm → Tm → M Bool
  | 0, _, _, _, _ => throw .fuel
  | n + 1, Γ, l, I, D => do
    match ← whnf E n Γ D with
    | .dret _ => pure true
    | .drec _ _ D₁ => inertDesc E n Γ l I D₁
    | .darg _ S D₁ =>
      match ← tagField E n Γ S with
      | some (k, lifted) => inertTags E n Γ l I D₁ k lifted k
      | none =>
        if ← inert E n Γ S then inertDesc E n (S :: Γ) l I.shift (.app D₁.shift (.var 0)) else pure false
    | _ => pure false

/-- `inertDesc` of `D₁ tag` for each of the first `j` tags. -/
def inertTags (E : Env) : Nat → Ctx → Lvl → Tm → Tm → Nat → Bool → Nat → M Bool
  | 0, _, _, _, _, _, _, _ => throw .fuel
  | _ + 1, _, _, _, _, _, _, 0 => pure true
  | n + 1, Γ, l, I, D₁, k, lifted, j + 1 => do
    let t : Tm := if lifted then .up (.tag k j) else .tag k j
    if ← inertDesc E n Γ l I (.app D₁ t) then inertTags E n Γ l I D₁ k lifted j else pure false

/-- `Γ ⊢ t ≡ u : T`, for well-typed `t`, `u`. -/
def conv (E : Env) : Nat → Ctx → Tm → Tm → Tm → M Bool
  | 0, _, _, _, _ => throw .fuel
  | n + 1, Γ, T, t, u => do
    let T' ← whnfS E n Γ T
    -- proof irrelevance, before either side is looked at
    if (← sortOf E n Γ T').isZero then pure true else
    match T' with
    | .pi _ _ A B => conv E n (A :: Γ) B (.app t.shift (.var 0)) (.app u.shift (.var 0))
    | .sigma _ _ A B => do
      if ← conv E n Γ A (.fst t) (.fst u) then conv E n Γ (B.inst (.fst t)) (.snd t) (.snd u)
      else pure false
    | .unit _ => pure true
    | .ulift _ A => conv E n Γ A (.down t) (.down u)
    | .sort _ => convTy E n Γ t u
    | _ => do
      let t' ← whnfS E n Γ t
      let u' ← whnfS E n Γ u
      match T', t', u' with
      | .enum _, .tag _ i, .tag _ j => pure (i == j)
      | .qty, .qlit q, .qlit q' => pure (q == q')
      | .desc _ I, .dret i, .dret i' => conv E n Γ I i i'
      | .desc l I, .darg q S D, .darg q' S' D' =>
        if !(← conv E n Γ .qty q q') then pure false
        else if !(← convTy E n Γ S S') then pure false
        else conv E n Γ (.pi .many (some l.succ.succ) S (.desc l I.shift)) D D'
      | .desc l I, .drec q j D, .drec q' j' D' =>
        if !(← conv E n Γ .qty q q') then pure false
        else if !(← conv E n Γ I j j') then pure false
        else conv E n Γ (.desc l I) D D'
      | .desc l I, .dhrec q H j D, .dhrec q' H' j' D' =>
        if !(← conv E n Γ .qty q q') then pure false
        else if !(← convTy E n Γ H H') then pure false
        else if !(← conv E n Γ (.pi .many (some l.succ) H I.shift) j j') then pure false
        else conv E n Γ (.desc l I) D D'
      | .mu l I D i, .con x, .con y => conv E n Γ (.interp l I D (muFamily l I D) i) x y
      | _, _, _ => do pure (← convNe E n Γ t' u').isSome

/-- `Γ ⊢ A ≡ B` for two well-formed types. Structural: two propositions are compared like
any other types (their *equation* is what compares them by equivalence). -/
def convTy (E : Env) : Nat → Ctx → Tm → Tm → M Bool
  | 0, _, _, _ => throw .fuel
  | n + 1, Γ, A, B => do
    let A' ← whnfS E n Γ A
    let B' ← whnfS E n Γ B
    match A', B' with
    | .sort u, .sort w => pure (u.equiv w)
    | .pi q _ A₁ B₁, .pi q' _ A₂ B₂ =>
      if q != q' then pure false
      else if !(← convTy E n Γ A₁ A₂) then pure false
      else convTy E n (A₁ :: Γ) B₁ B₂
    | .sigma q _ A₁ B₁, .sigma q' _ A₂ B₂ =>
      if q != q' then pure false
      else if !(← convTy E n Γ A₁ A₂) then pure false
      else convTy E n (A₁ :: Γ) B₁ B₂
    | .unit u, .unit w => pure (u.equiv w)
    | .empty u, .empty w => pure (u.equiv w)
    | .enum k, .enum k' => pure (k == k')
    | .qty, .qty => pure true
    | .ulift u A₀, .ulift w B₀ => if u.equiv w then convTy E n Γ A₀ B₀ else pure false
    | .eq A₁ a b, .eq A₂ a' b' =>
      if !(← convTy E n Γ A₁ A₂) then pure false
      else if !(← conv E n Γ A₁ a a') then pure false
      else conv E n Γ A₁ b b'
    | .eqTy A₁ B₁, .eqTy A₂ B₂ =>
      if !(← convTy E n Γ A₁ A₂) then pure false else convTy E n Γ B₁ B₂
    | .desc l I, .desc l' I' => if l.equiv l' then convTy E n Γ I I' else pure false
    | .mu l I D i, .mu l' I' D' i' =>
      if !l.equiv l' then pure false
      else if !(← convTy E n Γ I I') then pure false
      else if !(← conv E n Γ (.desc l I) D D') then pure false
      else conv E n Γ I i i'
    | .interp l I D X i, .interp l' I' D' X' i' =>
      -- stuck on a neutral description (or a neutral field quantity)
      if !l.equiv l' then pure false
      else if !(← convTy E n Γ I I') then pure false
      else if !(← conv E n Γ (.desc l I) D D') then pure false
      else if !(← conv E n Γ (.pi .many (some l.succ.succ) I (.sort l.succ)) X X') then pure false
      else conv E n Γ I i i'
    | _, _ => do pure (← convNe E n Γ A' B').isSome

/-- Two neutral terms in weak-head normal form: equal heads and convertible arguments.
Returns their type. -/
def convNe (E : Env) : Nat → Ctx → Tm → Tm → M (Option Tm)
  | 0, _, _, _ => throw .fuel
  | n + 1, Γ, t, u =>
    match t, u with
    | .var i, .var j =>
      if i != j then pure none else
      match Γ.lookup i with
      | some T => pure (some T)
      | none => fail s!"variable {i} out of scope"
    | .const c us, .const c' us' =>
      if c != c' || us.length != us'.length || !(us.zip us').all (fun (a, b) => a.equiv b) then pure none else
      match E.sig.find? c with
      | some d => pure (some (d.type.instL us))
      | none => fail s!"unknown constant {c}"
    | .app f a, .app f' a' => do
      let some T ← convNe E n Γ f f' | pure none
      match ← whnfS E n Γ T with
      | .pi _ _ A B => if ← conv E n Γ A a a' then pure (some (B.inst a)) else pure none
      | _ => fail "convNe: not a function"
    | .fst p, .fst p' => do
      let some T ← convNe E n Γ p p' | pure none
      match ← whnfS E n Γ T with
      | .sigma _ _ A _ => pure (some A)
      | _ => fail "convNe: not a pair"
    | .snd p, .snd p' => do
      let some T ← convNe E n Γ p p' | pure none
      match ← whnfS E n Γ T with
      | .sigma _ _ _ B => pure (some (B.inst (.fst p)))
      | _ => fail "convNe: not a pair"
    | .down p, .down p' => do
      let some T ← convNe E n Γ p p' | pure none
      match ← whnfS E n Γ T with
      | .ulift _ A => pure (some A)
      | _ => fail "convNe: not a lift"
    | .absurd mot p, .absurd mot' p' => do
      if !(← convTy E n Γ mot mot') then pure none else
      -- the scrutinee, at its own type (`Empty_l`: irrelevant when `l` is `0`)
      let T ← typeOfNe E n Γ p
      if ← conv E n Γ T p p' then pure (some mot) else pure none
    | .ecase mot s bs, .ecase mot' s' bs' => do
      let some T ← convNe E n Γ s s' | pure none
      match ← whnfS E n Γ T with
      | .enum k =>
        if !(← convTy E n (.enum k :: Γ) mot mot') then pure none
        else if ← convBranches E n Γ mot k 0 bs bs' then pure (some (mot.inst s)) else pure none
      | _ => fail "convNe: not an enumeration"
    | .cast A B _ a, .cast A' B' _ a' => do
      -- the proofs are not compared
      if !(← convTy E n Γ A A') then pure none
      else if !(← convTy E n Γ B B') then pure none
      else if ← conv E n Γ A a a' then pure (some B) else pure none
    | .delim v P a b c h D, .delim v' P' a' b' c' h' D' => do
      let some T ← convNe E n Γ D D' | pure none
      match ← whnfS E n Γ T with
      | .desc l I =>
        if !v.equiv v' then pure none
        else if !(← conv E n Γ (delimMotiveTy l v I) P P') then pure none else
        let (ta, tb, tc, th) := delimMethodTys l v I P
        if !(← conv E n Γ ta a a') then pure none
        else if !(← conv E n Γ tb b b') then pure none
        else if !(← conv E n Γ tc c c') then pure none
        else if !(← conv E n Γ th h h') then pure none
        else pure (some (.app P D))
      | _ => fail "convNe: not a description"
    | .ind _ _ _ v P m _ x, .ind _ _ _ v' P' m' _ x' => do
      let some T ← convNe E n Γ x x' | pure none
      match ← whnfS E n Γ T with
      | .mu l I D i =>
        if !v.equiv v' then pure none
        else if !(← conv E n Γ (indMotiveTy l v I D) P P') then pure none
        else if !(← conv E n Γ (indMethodTy l v I D P) m m') then pure none
        else pure (some (apps P [i, x]))
      | _ => fail "convNe: not a data type"
    | _, _ => pure none

/-- The branches from the `i`-th on, each at the motive instantiated with its tag. -/
def convBranches (E : Env) : Nat → Ctx → Tm → Nat → Nat → Tm → Tm → M Bool
  | 0, _, _, _, _, _, _ => throw .fuel
  | n + 1, Γ, mot, k, i, bs, bs' =>
    match bs, bs' with
    | .bnil, .bnil => pure true
    | .bcons b r, .bcons b' r' => do
      if ← conv E n Γ (mot.inst (.tag k i)) b b' then convBranches E n Γ mot k (i + 1) r r'
      else pure false
    | _, _ => pure false

/-- `Γ ⊢ A : Sort l`: returns `l`. -/
def inferSort (E : Env) : Nat → Ctx → Tm → M Lvl
  | 0, _, _ => throw .fuel
  | n + 1, Γ, A => do
    match ← whnfS E n Γ (← infer E n Γ A) with
    | .sort l => pure l
    | _ => fail "not a type"

/-- The domain of an equation: a type, at a sort that is never `Prop` if the kernels' rule
is asked for. -/
def inferEqDomain (E : Env) : Nat → Ctx → Tm → M Unit
  | 0, _, _ => throw .fuel
  | n + 1, Γ, A => do
    let l ← inferSort E n Γ A
    if E.opts.eqNeverZero && !l.neverZero then fail "an equation at a type that may be a proposition"

/-- `Γ ⊢ t ⇒ T`. -/
def infer (E : Env) : Nat → Ctx → Tm → M Tm
  | 0, _, _ => throw .fuel
  | n + 1, Γ, t =>
    match t with
    | .var i =>
      match Γ.lookup i with
      | some T => pure T
      | none => fail s!"variable {i} out of scope"
    | .const c us =>
      match E.sig.find? c with
      | some d =>
        if us.length != d.nparams then fail s!"{c}: wrong number of universe levels"
        else pure (d.type.instL us)
      | none => fail s!"unknown constant {c}"
    | .sort l => pure (.sort l.succ)
    | .pi _ s A B => do
      let i ← inferSort E n Γ A
      let j ← inferSort E n (A :: Γ) B
      let r := Lvl.imax i j
      match s with
      | some s => if s.equiv r then pure (.sort r) else fail "Π: wrong sort annotation"
      | none => if E.opts.sortsOptional then pure (.sort r) else fail "Π without its sort"
    | .sigma _ s A B => do
      let i ← inferSort E n Γ A
      let j ← inferSort E n (A :: Γ) B
      let r := Lvl.max i j
      match s with
      | some s => if s.equiv r then pure (.sort r) else fail "Σ: wrong sort annotation"
      | none => if E.opts.sortsOptional then pure (.sort r) else fail "Σ without its sort"
    | .app f a => do
      match ← whnfS E n Γ (← infer E n Γ f) with
      | .pi _ _ A B => do
        check E n Γ a A
        pure (B.inst a)
      | _ => fail "application of a non-function"
    | .letE _ A v b => do
      let _ ← inferSort E n Γ A
      check E n Γ v A
      infer E n Γ (b.inst v)
    | .ann t A => do
      let _ ← inferSort E n Γ A
      check E n Γ t A
      pure A
    | .fst p => do
      match ← whnfS E n Γ (← infer E n Γ p) with
      | .sigma _ _ A _ => pure A
      | _ => fail "projection of a non-pair"
    | .snd p => do
      match ← whnfS E n Γ (← infer E n Γ p) with
      | .sigma _ _ _ B => pure (B.inst (.fst p))
      | _ => fail "projection of a non-pair"
    | .unit l => pure (.sort l)
    | .empty l => pure (.sort l)
    | .absurd mot p => do
      let _ ← inferSort E n Γ mot
      match ← whnfS E n Γ (← infer E n Γ p) with
      | .empty _ => pure mot
      | _ => fail "absurd: not a proof of an empty type"
    | .enum _ => pure (.sort 1)
    | .tag k i => if i < k then pure (.enum k) else fail "tag out of range"
    | .ecase mot s bs => do
      match ← whnfS E n Γ (← infer E n Γ s) with
      | .enum k => do
        let _ ← inferSort E n (.enum k :: Γ) mot
        checkBranches E n Γ mot k 0 bs
        pure (mot.inst s)
      | _ => fail "case on a non-enumeration"
    | .eq A a b => do
      inferEqDomain E n Γ A
      check E n Γ a A
      check E n Γ b A
      pure (.sort 0)
    | .eqTy A B => do
      let l ← inferSort E n Γ A
      let l' ← inferSort E n Γ B
      if l.equiv l' then pure (.sort 0) else fail "type equation between different universes"
    | .refl A a => do
      inferEqDomain E n Γ A
      check E n Γ a A
      pure (.eq A a a)
    | .reflTy A => do
      let _ ← inferSort E n Γ A
      pure (.eqTy A A)
    | .cast A B e a => do
      let l ← inferSort E n Γ A
      let l' ← inferSort E n Γ B
      if !l.equiv l' then fail "cast between different universes" else
      check E n Γ e (.eqTy A B)
      check E n Γ a A
      pure B
    | .transp A a P p b e => do
      inferEqDomain E n Γ A
      check E n Γ a A
      check E n Γ b A
      -- P : (0 b : A) → (0 _ : a =_A b) → Prop
      check E n Γ P (.pi .zero (some 1) A (.pi .zero (some 1) (.eq A.shift a.shift (.var 0)) (.sort 0)))
      check E n Γ p (.app (.app P a) (.refl A a))
      check E n Γ e (.eq A a b)
      pure (.app (.app P b) e)
    | .ulift l A => do
      let k ← inferSort E n Γ A
      if k.le l then pure (.sort l) else fail "ULift to a smaller universe"
    | .down p => do
      match ← whnfS E n Γ (← infer E n Γ p) with
      | .ulift _ A => pure A
      | _ => fail "down of a non-lift"
    | .qty => pure (.sort 1)
    | .qlit _ => pure .qty
    | .desc l I => do
      checkIndexLevel E n Γ l I
      pure (.sort l.succ.succ)
    | .mu l I D i => do
      checkIndexLevel E n Γ l I
      check E n Γ D (.desc l I)
      check E n Γ i I
      pure (.sort l.succ)
    | .interp l I D X i => do
      checkIndexLevel E n Γ l I
      check E n Γ D (.desc l I)
      check E n Γ X (.pi .many (some l.succ.succ) I (.sort l.succ))
      check E n Γ i I
      pure (.sort l.succ)
    | .delim v P mret marg mrec mhrec D => do
      match ← whnfS E n Γ (← infer E n Γ D) with
      | .desc l I => do
        check E n Γ P (delimMotiveTy l v I)
        let (ta, tb, tc, th) := delimMethodTys l v I P
        check E n Γ mret ta
        check E n Γ marg tb
        check E n Γ mrec tc
        check E n Γ mhrec th
        pure (.app P D)
      | _ => fail "Desc.elim on a non-description"
    | .ind l I D v P m i x => do
      -- the index type is in the family's own universe (audit F3)
      checkIndexLevel E n Γ l I
      check E n Γ D (.desc l I)
      check E n Γ P (indMotiveTy l v I D)
      check E n Γ m (indMethodTy l v I D P)
      check E n Γ i I
      check E n Γ x (.mu l I D i)
      pure (apps P [i, x])
    | _ => fail "cannot infer a type for this term"

/-- `Γ ⊢ I : Sort (l+1)`, exactly: the index type of `Desc.{l}`, `μ.{l}` and their
eliminators. -/
def checkIndexLevel (E : Env) : Nat → Ctx → Lvl → Tm → M Unit
  | 0, _, _, _ => throw .fuel
  | n + 1, Γ, l, I => do
    let k ← inferSort E n Γ I
    if k.equiv l.succ then pure () else fail "the index type is not in Sort (l+1)"

/-- `Γ ⊢ t ⇐ T`, for a well-formed type `T`. -/
def check (E : Env) : Nat → Ctx → Tm → Tm → M Unit
  | 0, _, _, _ => throw .fuel
  | n + 1, Γ, t, T => do
    let T' ← whnfS E n Γ T
    match t, T' with
    | .lam b, .pi _ _ A B => check E n (A :: Γ) b B
    | .pair a b, .sigma _ _ A B => do
      check E n Γ a A
      check E n Γ b (B.inst a)
    | .tt, .unit _ => pure ()
    | .up a, .ulift _ A => check E n Γ a A
    | .letE _ A v b, _ => do
      let _ ← inferSort E n Γ A
      check E n Γ v A
      check E n Γ (b.inst v) T'
    | .dret i, .desc _ I => check E n Γ i I
    | .darg q S D, .desc l I => do
      check E n Γ q .qty
      -- a field is in exactly Sort (l+1)
      checkIndexLevel E n Γ l S
      check E n Γ D (.pi .many (some l.succ.succ) S (.desc l I.shift))
    | .drec q j D, .desc l I => do
      check E n Γ q .qty
      check E n Γ j I
      check E n Γ D (.desc l I)
    | .dhrec q H j D, .desc l I => do
      check E n Γ q .qty
      checkIndexLevel E n Γ l H
      check E n Γ j (.pi .many (some l.succ) H I.shift)
      check E n Γ D (.desc l I)
    | .con x, .mu l I D i => check E n Γ x (.interp l I D (muFamily l I D) i)
    | _, _ => do
      let T₁ ← infer E n Γ t
      if ← convTy E n Γ T₁ T' then pure () else fail "type mismatch"

/-- The branches from the `i`-th on: exactly `k` of them, each at the motive instantiated
with its tag. -/
def checkBranches (E : Env) : Nat → Ctx → Tm → Nat → Nat → Tm → M Unit
  | 0, _, _, _, _, _ => throw .fuel
  | n + 1, Γ, mot, k, i, bs =>
    match bs with
    | .bnil => if i == k then pure () else fail "case: too few branches"
    | .bcons b r => do
      if i ≥ k then fail "case: too many branches" else
      check E n Γ b (mot.inst (.tag k i))
      checkBranches E n Γ mot k (i + 1) r
    | _ => fail "case: malformed branches"

end

/-! ## Entry points -/

def defaultFuel : Nat := 3000

/-- Add a declaration, checked with its level parameters symbolic: the name is new, the
type is a type, the value has it. -/
def addDecl (sg : Sig) (d : Decl) (opts : Opts := {}) (fuel : Nat := defaultFuel) : M Sig := do
  if (sg.find? d.name).isSome then fail s!"{d.name} is already declared"
  if d.type.lvlBound > d.nparams then fail s!"{d.name}: undeclared universe parameter in the type"
  let E : Env := { sig := sg, opts }
  let _ ← inferSort E fuel [] d.type
  match d.value with
  | some v =>
    if v.lvlBound > d.nparams then fail s!"{d.name}: undeclared universe parameter in the value"
    check E fuel [] v d.type
  | none => pure ()
  pure (d :: sg)

/-- The type of a closed term. -/
def inferClosed (sg : Sig) (t : Tm) (opts : Opts := {}) (fuel : Nat := defaultFuel) : M Tm :=
  if t.lvlBound > 0 then fail "universe parameter in a closed term"
  else infer { sig := sg, opts } fuel [] t

end WizMeta
