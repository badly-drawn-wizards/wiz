import WizMeta.Spec.Rule

/-!
# μ, constructors, induction

`μ.{l} I D i : Sort (l+1)` (no inductive propositions; no sizes: this is `μ^∞`).

* **The level premise on the eliminator** (audit F3): `ind` requires `I : Sort (l+1)`,
  as the formers do, so the types it builds are types the formers accept.
* **Equations between constructors compute by the description** (`Jdg.peq`): `ret` gives
  `True`; a tag field with two canonical tags continues at that constructor's
  description if they are equal, and is the `Σ` rule if they differ; a recursive field
  gives the field's equation, paired with the rest unless the rest is `ret`.
* **A field at a type that is not a tag type takes the `Σ` rule only when that type is
  canonical.** At a neutral field type the equation is stuck. The kernels take the `Σ`
  rule there too, and a substitution that turns the field type into an `Enum` then
  changes which rule applies, to a result that is equivalent but not convertible
  (model-memo row E5b, audit E7). So in the kernels a substitution instance of a
  well-typed term can be ill typed; the spec's rule is the stable one.
* The function type in the equation of an `hrec` field is the payload's own
  (`(ω h : H) → X (j h)`), not one carrying the field's quantity (row E5f).

Not here: `μ I D i ≡ μ I' D' i'` and casts at `μ` (PR #40's rules by codes are not on
master; master's rule compares the two families syntactically, which is not a rule the
spec can state). In the spec both are stuck, and T1 identifies a cast between
convertible inert `μ` types with its argument.
-/

namespace WizMeta.Spec
set_option autoImplicit true

/-- A canonical type that is not a tag type (`Enum`, or a lift of one). -/
def NonTag (S : Tm) : Prop :=
  ∃ f, S.former? = some f ∧ f ≠ .enum ∧
    ∀ u A, S = .ulift u A → ∃ g, A.former? = some g ∧ g ≠ .enum

/-- A description that is visibly not `ret`. -/
def NonRet : Tm → Prop
  | .darg .. | .drec .. | .dhrec .. => True
  | _ => False

inductive Mu : Rules
  | form : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ i ∶ I], Γ ⊢ .mu l I D i ∶ .sort l.succ⟩
  | con : Mu ⟨[Γ ⊢ .mu l I D i ∶ .sort l.succ, Γ ⊢ x ∶ .interp l I D (.muFamily l I D) i],
      Γ ⊢ .con x ∶ .mu l I D i⟩
  | ind : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ P ∶ .indMotiveTy l v I D,
        Γ ⊢ m ∶ .indMethodTy l v I D P, Γ ⊢ i ∶ I, Γ ⊢ x ∶ .mu l I D i],
      Γ ⊢ .ind l I D v P m i x ∶ .apps P [i, x]⟩
  | iota : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ P ∶ .indMotiveTy l v I D,
        Γ ⊢ m ∶ .indMethodTy l v I D P, Γ ⊢ i ∶ I, Γ ⊢ .con xs ∶ .mu l I D i],
      Γ ⊢ .ind l I D v P m i (.con xs) ⟶ .indCon l v I D P m i xs ∶ .apps P [i, .con xs]⟩
  | indRed : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ P ∶ .indMotiveTy l v I D,
        Γ ⊢ m ∶ .indMethodTy l v I D P, Γ ⊢ i ∶ I, Γ ⊢ x ⟶ x' ∶ .mu l I D i],
      Γ ⊢ .ind l I D v P m i x ⟶ .ind l I D v P m i x' ∶ .apps P [i, x]⟩
  | cong : l.Equiv l' →
      Mu ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ i ≡ i' ∶ I],
        Γ ⊢ .mu l I D i ≡ .mu l' I' D' i' ∶ .sort l.succ⟩
  | conCong : Mu ⟨[Γ ⊢ .mu l I D i ∶ .sort l.succ, Γ ⊢ x ≡ y ∶ .interp l I D (.muFamily l I D) i],
      Γ ⊢ .con x ≡ .con y ∶ .mu l I D i⟩
  | indCong : l.Equiv l' → v.Equiv v' →
      Mu ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ P ≡ P' ∶ .indMotiveTy l v I D,
          Γ ⊢ m ≡ m' ∶ .indMethodTy l v I D P, Γ ⊢ i ≡ i' ∶ I, Γ ⊢ x ≡ x' ∶ .mu l I D i],
        Γ ⊢ .ind l I D v P m i x ≡ .ind l' I' D' v' P' m' i' x' ∶ .apps P [i, x]⟩
  -- equations between constructors
  | eq : Mu ⟨[Γ ⊢ .con x ∶ .mu l I D i, Γ ⊢ .con y ∶ .mu l I D i, .peq Γ l I (.muFamily l I D) i D x y r],
      Γ ⊢ .eq (.mu l I D i) (.con x) (.con y) ⟶ r ∶ .sort 0⟩
  | eqRedL : Mu ⟨[Γ ⊢ a ⟶ a' ∶ .mu l I D i, Γ ⊢ b ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) a b ⟶ .eq (.mu l I D i) a' b ∶ .sort 0⟩
  | eqRedR : Mu ⟨[Γ ⊢ a ∶ .mu l I D i, Γ ⊢ b ⟶ b' ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) a b ⟶ .eq (.mu l I D i) a b' ∶ .sort 0⟩
  | peqRet : Mu ⟨[Γ ⊢ D ≡ .dret j ∶ .desc l I], .peq Γ l I X i D x y .True'⟩
  /-- a tag field, the same canonical tag on both sides -/
  | peqTag : Mu ⟨[Γ ⊢ D ≡ .darg q (.enum k) E ∶ .desc l I, Γ ⊢ .fst x ≡ .tag k a ∶ .enum k,
        Γ ⊢ .fst y ≡ .tag k a ∶ .enum k, .peq Γ l I X i (.app E (.tag k a)) (.snd x) (.snd y) r],
      .peq Γ l I X i D x y r⟩
  | peqTagLifted : Mu ⟨[Γ ⊢ D ≡ .darg q (.ulift u (.enum k)) E ∶ .desc l I, Γ ⊢ .down (.fst x) ≡ .tag k a ∶ .enum k,
        Γ ⊢ .down (.fst y) ≡ .tag k a ∶ .enum k, .peq Γ l I X i (.app E (.up (.tag k a))) (.snd x) (.snd y) r],
      .peq Γ l I X i D x y r⟩
  /-- two different canonical tags: the `Σ` rule (whose first component is `False`) -/
  | peqTagDiff : a ≠ b →
      Mu ⟨[Γ ⊢ D ≡ .darg q (.enum k) E ∶ .desc l I, Γ ⊢ .fst x ≡ .tag k a ∶ .enum k, Γ ⊢ .fst y ≡ .tag k b ∶ .enum k],
        .peq Γ l I X i D x y (.eq (.interp l I (.darg q (.enum k) E) X i) x y)⟩
  | peqTagLiftedDiff : a ≠ b →
      Mu ⟨[Γ ⊢ D ≡ .darg q (.ulift u (.enum k)) E ∶ .desc l I, Γ ⊢ .down (.fst x) ≡ .tag k a ∶ .enum k,
          Γ ⊢ .down (.fst y) ≡ .tag k b ∶ .enum k],
        .peq Γ l I X i D x y (.eq (.interp l I (.darg q (.ulift u (.enum k)) E) X i) x y)⟩
  /-- a field at a canonical type that is not a tag type: the `Σ` rule -/
  | peqField : NonTag S →
      Mu ⟨[Γ ⊢ D ≡ .darg q S E ∶ .desc l I], .peq Γ l I X i D x y (.eq (.interp l I (.darg q S E) X i) x y)⟩
  | peqRecLast : Mu ⟨[Γ ⊢ D ≡ .drec q j (.dret j') ∶ .desc l I], .peq Γ l I X i D x y (.eq (.app X j) (.fst x) (.fst y))⟩
  | peqRec : NonRet E →
      Mu ⟨[Γ ⊢ D ≡ .drec q j E ∶ .desc l I, .peq Γ l I X i E (.snd x) (.snd y) r],
        .peq Γ l I X i D x y (.sigma .zero (some 0) (.eq (.app X j) (.fst x) (.fst y)) r.shift)⟩
  | peqHrecLast : Mu ⟨[Γ ⊢ D ≡ .dhrec q H j (.dret j') ∶ .desc l I],
      .peq Γ l I X i D x y (.eq (.hrecFieldTy l H j X) (.fst x) (.fst y))⟩
  | peqHrec : NonRet E →
      Mu ⟨[Γ ⊢ D ≡ .dhrec q H j E ∶ .desc l I, .peq Γ l I X i E (.snd x) (.snd y) r],
        .peq Γ l I X i D x y (.sigma .zero (some 0) (.eq (.hrecFieldTy l H j X) (.fst x) (.fst y)) r.shift)⟩

end WizMeta.Spec
