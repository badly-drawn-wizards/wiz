import WizMeta.Spec.Rule

/-!
# Π

`(q x : A) →^⟨i,j⟩ B` carries its quantity label and the sorts of its components (mandatory
sorts, as in both kernels); it is in `Sort (imax i j)` (impredicative at `Prop`). λ has no domain. β is a reduction; η is a conversion rule.
The quantity is part of the type's identity: no rule relates two `Π`s with different
labels, and their type equation is `False`.

The rule for an equation between two such types with the same quantity is in
`EqTyCross.lean` / `EqTyLevelled.lean` (two variants).
-/

namespace WizMeta.Spec

inductive Pi : Rules
  | form {Γ : Ctx} {A B : Tm} {σ : Sorts} {q : Q} :
      Pi ⟨[Γ ⊢ A ∶ .sort σ.dom, (A :: Γ) ⊢ B ∶ .sort σ.cod], Γ ⊢ .pi q (some σ) A B ∶ .sort σ.pi⟩
  -- `Γ ⊢ A ∶ Sort i` in the rules with a premise under the binder: the renaming lemma needs
  -- the binder's type typed to extend the target context (it is not reachable from
  -- `Γ ⊢ Π A B ∶ Sort s` without an inversion lemma)
  | lam {Γ : Ctx} {A B b : Tm} {σ : Sorts} {q : Q} :
      Pi ⟨[Γ ⊢ .pi q (some σ) A B ∶ .sort σ.pi, Γ ⊢ A ∶ .sort σ.dom, (A :: Γ) ⊢ b ∶ B], Γ ⊢ .lam b ∶ .pi q (some σ) A B⟩
  | app {Γ : Ctx} {f A B a : Tm} {σ : Sorts} {q : Q} : Pi ⟨[Γ ⊢ f ∶ .pi q (some σ) A B, Γ ⊢ a ∶ A], Γ ⊢ .app f a ∶ B.inst a⟩
  | beta {Γ : Ctx} {A B b a : Tm} {σ : Sorts} {q : Q} :
      Pi ⟨[Γ ⊢ .pi q (some σ) A B ∶ .sort σ.pi, Γ ⊢ A ∶ .sort σ.dom, (A :: Γ) ⊢ b ∶ B, Γ ⊢ a ∶ A],
      Γ ⊢ .app (.lam b) a ⟶ b.inst a ∶ B.inst a⟩
  | appRed {Γ : Ctx} {f f' A B a : Tm} {σ : Sorts} {q : Q} : Pi ⟨[Γ ⊢ f ⟶ f' ∶ .pi q (some σ) A B, Γ ⊢ a ∶ A], Γ ⊢ .app f a ⟶ .app f' a ∶ B.inst a⟩
  /-- η, as extensionality -/
  | eta {Γ : Ctx} {f A B g : Tm} {σ : Sorts} {q : Q} : Pi ⟨[Γ ⊢ f ∶ .pi q (some σ) A B, Γ ⊢ g ∶ .pi q (some σ) A B, Γ ⊢ A ∶ .sort σ.dom,
        (A :: Γ) ⊢ .app f.shift (.var 0) ≡ .app g.shift (.var 0) ∶ B],
      Γ ⊢ f ≡ g ∶ .pi q (some σ) A B⟩
  | cong {Γ : Ctx} {A A' B B' : Tm} {σ σ' : Sorts} {q : Q} : σ.dom.Equiv σ'.dom → σ.cod.Equiv σ'.cod →
      Pi ⟨[Γ ⊢ A ∶ .sort σ.dom, Γ ⊢ A ≡ A' ∶ .sort σ.dom, (A :: Γ) ⊢ B ≡ B' ∶ .sort σ.cod],
        Γ ⊢ .pi q (some σ) A B ≡ .pi q (some σ') A' B' ∶ .sort σ.pi⟩
  | appCong {Γ : Ctx} {f f' A B a a' : Tm} {σ : Sorts} {q : Q} : Pi ⟨[Γ ⊢ f ≡ f' ∶ .pi q (some σ) A B, Γ ⊢ a ≡ a' ∶ A], Γ ⊢ .app f a ≡ .app f' a' ∶ B.inst a⟩
  /-- funext: an equation between functions is pointwise -/
  | eq {Γ : Ctx} {A B f g : Tm} {σ : Sorts} {q : Q} : σ.pi.NeverZero →
      Pi ⟨[Γ ⊢ .pi q (some σ) A B ∶ .sort σ.pi, Γ ⊢ f ∶ .pi q (some σ) A B, Γ ⊢ g ∶ .pi q (some σ) A B],
        Γ ⊢ .eq (.pi q (some σ) A B) f g ⟶ .eqPi σ.dom A B f g ∶ .sort 0⟩
  /-- different quantities: different types -/
  | eqTyApart {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {σ₁ σ₂ : Sorts} {q q' : Q} : σ₁.pi.NeverZero → σ₂.pi.NeverZero → q ≠ q' →
      Pi ⟨[Γ ⊢ .pi q (some σ₁) A₁ B₁ ∶ .sort σ₁.pi, Γ ⊢ .pi q' (some σ₂) A₂ B₂ ∶ .sort σ₂.pi],
        Γ ⊢ .eqTy (.pi q (some σ₁) A₁ B₁) (.pi q' (some σ₂) A₂ B₂) ⟶ .False' ∶ .sort 0⟩
  /-- the reduct casts between the domains and between the codomains, so each pair is in one
  sort (a cast is formed at one sort): the D2 gate, `σ₁ ≡ σ₂` on the written sorts; otherwise
  the cast is stuck -/
  | cast {Γ : Ctx} {A₁ B₁ A₂ B₂ e t : Tm} {σ₁ σ₂ : Sorts} {q : Q} : σ₁.pi.NeverZero → σ₂.pi.NeverZero →
      σ₁.dom.Equiv σ₂.dom → σ₁.cod.Equiv σ₂.cod →
      Pi ⟨[Γ ⊢ .pi q (some σ₁) A₁ B₁ ∶ .sort σ₁.pi, Γ ⊢ .pi q (some σ₂) A₂ B₂ ∶ .sort σ₂.pi,
          Γ ⊢ A₁ ∶ .sort σ₁.dom, Γ ⊢ A₂ ∶ .sort σ₁.dom, (A₁ :: Γ) ⊢ B₁ ∶ .sort σ₁.cod, (A₂ :: Γ) ⊢ B₂ ∶ .sort σ₁.cod,
          Γ ⊢ e ∶ .eqTy (.pi q (some σ₁) A₁ B₁) (.pi q (some σ₂) A₂ B₂), Γ ⊢ t ∶ .pi q (some σ₁) A₁ B₁],
        Γ ⊢ .cast (.pi q (some σ₁) A₁ B₁) (.pi q (some σ₂) A₂ B₂) e t ⟶ .castPi A₁ B₁ A₂ B₂ e t
          ∶ .pi q (some σ₂) A₂ B₂⟩

end WizMeta.Spec
