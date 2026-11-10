import WizMeta.Spec.Rule

/-!
# Π

`(q x : A) → B` carries its quantity label and its sort `s ≡ imax i j` (mandatory;
impredicative at `Prop`). λ has no domain. β is a reduction; η is a conversion rule.
The quantity is part of the type's identity: no rule relates two `Π`s with different
labels, and their type equation is `False`.

The rule for an equation between two such types with the same quantity is in
`EqTyCross.lean` / `EqTyLevelled.lean` (two variants).
-/

namespace WizMeta.Spec
set_option autoImplicit true

inductive Pi : Rules
  | form : s.Equiv (.imax i j) →
      Pi ⟨[Γ ⊢ A ∶ .sort i, (A :: Γ) ⊢ B ∶ .sort j], Γ ⊢ .pi q (some s) A B ∶ .sort s⟩
  | lam : Pi ⟨[Γ ⊢ .pi q (some s) A B ∶ .sort s, (A :: Γ) ⊢ b ∶ B], Γ ⊢ .lam b ∶ .pi q (some s) A B⟩
  | app : Pi ⟨[Γ ⊢ f ∶ .pi q (some s) A B, Γ ⊢ a ∶ A], Γ ⊢ .app f a ∶ B.inst a⟩
  | beta : Pi ⟨[Γ ⊢ .pi q (some s) A B ∶ .sort s, (A :: Γ) ⊢ b ∶ B, Γ ⊢ a ∶ A],
      Γ ⊢ .app (.lam b) a ⟶ b.inst a ∶ B.inst a⟩
  | appRed : Pi ⟨[Γ ⊢ f ⟶ f' ∶ .pi q (some s) A B, Γ ⊢ a ∶ A], Γ ⊢ .app f a ⟶ .app f' a ∶ B.inst a⟩
  /-- η, as extensionality -/
  | eta : Pi ⟨[Γ ⊢ f ∶ .pi q (some s) A B, Γ ⊢ g ∶ .pi q (some s) A B,
        (A :: Γ) ⊢ .app f.shift (.var 0) ≡ .app g.shift (.var 0) ∶ B],
      Γ ⊢ f ≡ g ∶ .pi q (some s) A B⟩
  | cong : s.Equiv (.imax i j) → s'.Equiv (.imax i j) →
      Pi ⟨[Γ ⊢ A ≡ A' ∶ .sort i, (A :: Γ) ⊢ B ≡ B' ∶ .sort j],
        Γ ⊢ .pi q (some s) A B ≡ .pi q (some s') A' B' ∶ .sort s⟩
  | appCong : Pi ⟨[Γ ⊢ f ≡ f' ∶ .pi q (some s) A B, Γ ⊢ a ≡ a' ∶ A], Γ ⊢ .app f a ≡ .app f' a' ∶ B.inst a⟩
  /-- funext: an equation between functions is pointwise -/
  | eq : s.NeverZero →
      Pi ⟨[Γ ⊢ .pi q (some s) A B ∶ .sort s, Γ ⊢ f ∶ .pi q (some s) A B, Γ ⊢ g ∶ .pi q (some s) A B],
        Γ ⊢ .eq (.pi q (some s) A B) f g ⟶ .eqPi A B f g ∶ .sort 0⟩
  /-- different quantities: different types -/
  | eqTyApart : s₁.NeverZero → s₂.NeverZero → q ≠ q' →
      Pi ⟨[Γ ⊢ .pi q (some s₁) A₁ B₁ ∶ .sort s₁, Γ ⊢ .pi q' (some s₂) A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.pi q (some s₁) A₁ B₁) (.pi q' (some s₂) A₂ B₂) ⟶ .False' ∶ .sort 0⟩
  | cast : s₁.NeverZero → s₂.NeverZero →
      Pi ⟨[Γ ⊢ .pi q (some s₁) A₁ B₁ ∶ .sort s₁, Γ ⊢ .pi q (some s₂) A₂ B₂ ∶ .sort s₂,
          Γ ⊢ e ∶ .eqTy (.pi q (some s₁) A₁ B₁) (.pi q (some s₂) A₂ B₂), Γ ⊢ t ∶ .pi q (some s₁) A₁ B₁],
        Γ ⊢ .cast (.pi q (some s₁) A₁ B₁) (.pi q (some s₂) A₂ B₂) e t ⟶ .castPi A₁ B₁ A₂ B₂ e t
          ∶ .pi q (some s₂) A₂ B₂⟩

end WizMeta.Spec
