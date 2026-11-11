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
  | pi {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Lvl} {q : Q} : s₁.NeverZero → s₂.NeverZero →
      EqTyCross ⟨[Γ ⊢ .pi q (some s₁) A₁ B₁ ∶ .sort s₁, Γ ⊢ .pi q (some s₂) A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.pi q (some s₁) A₁ B₁) (.pi q (some s₂) A₂ B₂) ⟶ .eqTyPi A₁ B₁ A₂ B₂ ∶ .sort 0⟩
  | sigma {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Lvl} {q : Q} : s₁.NeverZero → s₂.NeverZero →
      EqTyCross ⟨[Γ ⊢ .sigma q (some s₁) A₁ B₁ ∶ .sort s₁, Γ ⊢ .sigma q (some s₂) A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.sigma q (some s₁) A₁ B₁) (.sigma q (some s₂) A₂ B₂) ⟶ .eqTySigma A₁ B₁ A₂ B₂ ∶ .sort 0⟩

end WizMeta.Spec
