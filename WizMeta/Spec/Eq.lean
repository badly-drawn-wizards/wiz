import WizMeta.Spec.Rule

/-!
# Observational equality: formation, proofs, and the rules that do not belong to a former

`a =_A b` and `A ≡ B` are propositions that compute: by the type `A` (each former's file
has its rule), and here

* at a proposition `A`, `a =_A b ⟶ True`;
* two propositions are equal when equivalent: `P ≡ Q ⟶ (P → Q) × (Q → P)`;
* two different canonical formers (neither type a proposition) are not equal.

`refl`, `reflTy`, `transp` are proofs and have no rules. `cast` is the one operation with
a relevant result; its rules are in the formers' files, and here its congruence, which
does **not** compare the proofs.

**Formation.** `a =_A b` is formed at any sort. The kernels form it only at a sort that is
never `Prop`, but the reducts of their own rules contain equations at propositions (the
`Σ` rule at a proof component), so with that restriction a reduct of a well-formed type
is not well formed. (`Opts.kernelEqFormation` in the checker restores the restriction.)
The formation of `A ≡ B` is in the two `EqTy…` files.
-/

namespace WizMeta.Spec
set_option autoImplicit true

inductive Eq : Rules
  | eq : Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A], Γ ⊢ .eq A a b ∶ .sort 0⟩
  | refl : Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .refl A a ∶ .eq A a a⟩
  | reflTy : Eq ⟨[Γ ⊢ A ∶ .sort l], Γ ⊢ .reflTy A ∶ .eqTy A A⟩
  /-- transport into a `Prop`-valued family; with `cast` it gives J -/
  | transp : Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A, Γ ⊢ P ∶ .transpMotiveTy A a,
        Γ ⊢ p ∶ .app (.app P a) (.refl A a), Γ ⊢ e ∶ .eq A a b],
      Γ ⊢ .transp A a P p b e ∶ .app (.app P b) e⟩
  | cast : Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A], Γ ⊢ .cast A B e t ∶ B⟩
  | eqCong : Eq ⟨[Γ ⊢ A ≡ A' ∶ .sort l, Γ ⊢ a ≡ a' ∶ A, Γ ⊢ b ≡ b' ∶ A], Γ ⊢ .eq A a b ≡ .eq A' a' b' ∶ .sort 0⟩
  | eqTyCong : Eq ⟨[Γ ⊢ A ≡ A' ∶ .sort l, Γ ⊢ B ≡ B' ∶ .sort l'], Γ ⊢ .eqTy A B ≡ .eqTy A' B' ∶ .sort 0⟩
  /-- the proofs `e`, `e'` are not compared -/
  | castCong : Eq ⟨[Γ ⊢ A ≡ A' ∶ .sort l, Γ ⊢ B ≡ B' ∶ .sort l, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ e' ∶ .eqTy A' B',
        Γ ⊢ t ≡ t' ∶ A],
      Γ ⊢ .cast A B e t ≡ .cast A' B' e' t' ∶ B⟩
  -- weak-head reduction looks at the type of an equation, and at the two types of a cast
  | eqRed : Eq ⟨[Γ ⊢ A ⟶ A' ∶ .sort l, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A], Γ ⊢ .eq A a b ⟶ .eq A' a b ∶ .sort 0⟩
  | eqTyRedL : Eq ⟨[Γ ⊢ A ⟶ A' ∶ .sort l, Γ ⊢ B ∶ .sort l'], Γ ⊢ .eqTy A B ⟶ .eqTy A' B ∶ .sort 0⟩
  | eqTyRedR : Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ⟶ B' ∶ .sort l'], Γ ⊢ .eqTy A B ⟶ .eqTy A B' ∶ .sort 0⟩
  | castRedL : Eq ⟨[Γ ⊢ A ⟶ A' ∶ .sort l, Γ ⊢ B ∶ .sort l, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A],
      Γ ⊢ .cast A B e t ⟶ .cast A' B e t ∶ B⟩
  | castRedR : Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ⟶ B' ∶ .sort l, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A],
      Γ ⊢ .cast A B e t ⟶ .cast A B' e t ∶ B⟩
  /-- an equation between two proofs -/
  | eqAtProp : l.IsZero → Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A], Γ ⊢ .eq A a b ⟶ .True' ∶ .sort 0⟩
  /-- two propositions are equal when equivalent, whatever their shapes -/
  | eqTyProps : l.IsZero → l'.IsZero →
      Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l'], Γ ⊢ .eqTy A B ⟶ .iff A B ∶ .sort 0⟩
  /-- no confusion of type formers -/
  | eqTyFormers : l.NeverZero → l'.NeverZero → A.former? = some f → B.former? = some f' → f ≠ f' →
      Eq ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l'], Γ ⊢ .eqTy A B ⟶ .False' ∶ .sort 0⟩

end WizMeta.Spec
