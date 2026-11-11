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

inductive EqTyLevelled : Rules
  | form {Γ : Ctx} {A B : Tm} {l : Lvl} : EqTyLevelled ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l], Γ ⊢ .eqTy A B ∶ .sort 0⟩
  | pi {Γ : Ctx} {A₁ A₂ B₁ B₂ : Tm} {σ₁ σ₂ : Sorts} {q : Q} : σ₁.pi.NeverZero → σ₂.pi.NeverZero →
      σ₁.dom.Equiv σ₂.dom → σ₁.cod.Equiv σ₂.cod →
      EqTyLevelled ⟨[Γ ⊢ A₁ ∶ .sort σ₁.dom, Γ ⊢ A₂ ∶ .sort σ₁.dom, (A₁ :: Γ) ⊢ B₁ ∶ .sort σ₁.cod, (A₂ :: Γ) ⊢ B₂ ∶ .sort σ₁.cod],
        Γ ⊢ .eqTy (.pi q (some σ₁) A₁ B₁) (.pi q (some σ₂) A₂ B₂) ⟶ .eqTyPi σ₂.dom A₁ B₁ A₂ B₂ ∶ .sort 0⟩
  | sigma {Γ : Ctx} {A₁ A₂ B₁ B₂ : Tm} {σ₁ σ₂ : Sorts} {q : Q} : σ₁.sigma.NeverZero → σ₂.sigma.NeverZero →
      σ₁.dom.Equiv σ₂.dom → σ₁.cod.Equiv σ₂.cod →
      EqTyLevelled ⟨[Γ ⊢ A₁ ∶ .sort σ₁.dom, Γ ⊢ A₂ ∶ .sort σ₁.dom, (A₁ :: Γ) ⊢ B₁ ∶ .sort σ₁.cod, (A₂ :: Γ) ⊢ B₂ ∶ .sort σ₁.cod],
        Γ ⊢ .eqTy (.sigma q (some σ₁) A₁ B₁) (.sigma q (some σ₂) A₂ B₂) ⟶ .eqTySigma σ₁.dom A₁ B₁ A₂ B₂ ∶ .sort 0⟩

end WizMeta.Spec
