import WizMeta.Spec.Rule

/-!
# Type equations, variant "levelled" (CCobs's Eq-Π; not what the kernels implement)

`A ≡ B` is formed only between two types of one sort, and an equation between two `Π`
(or `Σ`) types decomposes only when the two domains are in one sort and the two
codomains are in one sort ([PT23] Fig. 4; its model tags `Π` codes with their levels).
Otherwise the equation is stuck: no rule. Every reduct is then again an equation at one
sort, so "a proposition against a type that is not one" never arises.

Not decided (model-memo, open question): whether two `Π` types whose domains are in
*different closed* sorts should be `False` here, as different codes are. This file says
nothing, which is the weaker choice.
-/

namespace WizMeta.Spec
set_option autoImplicit true

inductive EqTyLevelled : Rules
  | form : EqTyLevelled ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l], Γ ⊢ .eqTy A B ∶ .sort 0⟩
  | pi : s₁.NeverZero → s₂.NeverZero → s₁.Equiv (.imax i j) → s₂.Equiv (.imax i j) →
      EqTyLevelled ⟨[Γ ⊢ A₁ ∶ .sort i, Γ ⊢ A₂ ∶ .sort i, (A₁ :: Γ) ⊢ B₁ ∶ .sort j, (A₂ :: Γ) ⊢ B₂ ∶ .sort j],
        Γ ⊢ .eqTy (.pi q (some s₁) A₁ B₁) (.pi q (some s₂) A₂ B₂) ⟶ .eqTyPi A₁ B₁ A₂ B₂ ∶ .sort 0⟩
  | sigma : s₁.NeverZero → s₂.NeverZero → s₁.Equiv (.max i j) → s₂.Equiv (.max i j) →
      EqTyLevelled ⟨[Γ ⊢ A₁ ∶ .sort i, Γ ⊢ A₂ ∶ .sort i, (A₁ :: Γ) ⊢ B₁ ∶ .sort j, (A₂ :: Γ) ⊢ B₂ ∶ .sort j],
        Γ ⊢ .eqTy (.sigma q (some s₁) A₁ B₁) (.sigma q (some s₂) A₂ B₂) ⟶ .eqTySigma A₁ B₁ A₂ B₂ ∶ .sort 0⟩

end WizMeta.Spec
