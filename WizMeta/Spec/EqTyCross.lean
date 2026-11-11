import WizMeta.Spec.Rule

/-!
# Type equations, variant "cross-level" (what both kernels implement)

`A ≡ B` is formed for any two types, and an equation between two `Π` (or `Σ`) types
decomposes **without comparing the sorts of the two domains or of the two codomains**.
So the reduct can ask `A₂ ≡ A₁` for types in different universes, where it is `False`
between a proposition and a type that is not one, and otherwise decided by shape
(`Sort 0 ≡ Sort 1 ⟶ False`).

The kernels' *surface* rule forms `A ≡ B` only at one sort; their computation rules do
not keep to it (model-memo rows T4, T6; `((False → Nat) → Type) ≡ ((False → Type) → Type)`
is provable). This file takes the computation rules at face value and widens formation
so that reduction preserves typing. `EqTyLevelled.lean` is the other choice. A system
takes exactly one of the two.
-/

namespace WizMeta.Spec

inductive EqTyCross : Rules
  | form {Γ : Ctx} {A B : Tm} {l l' : Lvl} : EqTyCross ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l'], Γ ⊢ .eqTy A B ∶ .sort 0⟩
  /-- a proposition and a type that is not one -/
  | propType {Γ : Ctx} {A B : Tm} {l l' : Lvl} : l.IsZero → l'.NeverZero →
      EqTyCross ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l'], Γ ⊢ .eqTy A B ⟶ .False' ∶ .sort 0⟩
  | typeProp {Γ : Ctx} {A B : Tm} {l l' : Lvl} : l.NeverZero → l'.IsZero →
      EqTyCross ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ B ∶ .sort l'], Γ ⊢ .eqTy A B ⟶ .False' ∶ .sort 0⟩
  | pi {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {σ₁ σ₂ : Sorts} {q : Q} : σ₁.pi.NeverZero → σ₂.pi.NeverZero →
      EqTyCross ⟨[Γ ⊢ .pi q (some σ₁) A₁ B₁ ∶ .sort σ₁.pi, Γ ⊢ .pi q (some σ₂) A₂ B₂ ∶ .sort σ₂.pi],
        Γ ⊢ .eqTy (.pi q (some σ₁) A₁ B₁) (.pi q (some σ₂) A₂ B₂) ⟶ .eqTyPi σ₂.dom A₁ B₁ A₂ B₂ ∶ .sort 0⟩
  | sigma {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {σ₁ σ₂ : Sorts} {q : Q} : σ₁.sigma.NeverZero → σ₂.sigma.NeverZero →
      EqTyCross ⟨[Γ ⊢ .sigma q (some σ₁) A₁ B₁ ∶ .sort σ₁.sigma, Γ ⊢ .sigma q (some σ₂) A₂ B₂ ∶ .sort σ₂.sigma],
        Γ ⊢ .eqTy (.sigma q (some σ₁) A₁ B₁) (.sigma q (some σ₂) A₂ B₂) ⟶ .eqTySigma σ₁.dom A₁ B₁ A₂ B₂ ∶ .sort 0⟩

end WizMeta.Spec
