import WizMeta.Spec.Rule

/-!
# Σ

`(q x : A) ×^⟨i,j⟩ B` in `Sort (max i j)`, with its components' sorts written (mandatory
sorts; so a `Σ` of two propositions is one). Pairs,
projections, β as reductions, η as a conversion rule. No `split` (it is `Σ`-η plus `let`).

The rule for an equation between two such types with the same quantity is in
`EqTyCross.lean` / `EqTyLevelled.lean` (two variants).
-/

namespace WizMeta.Spec

inductive Sigma : Rules
  | form {Γ : Ctx} {A B : Tm} {σ : Sorts} {q : Q} :
      Sigma ⟨[Γ ⊢ A ∶ .sort σ.dom, (A :: Γ) ⊢ B ∶ .sort σ.cod], Γ ⊢ .sigma q (some σ) A B ∶ .sort σ.sigma⟩
  | pair {Γ : Ctx} {A B a b : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ .sigma q (some σ) A B ∶ .sort σ.sigma, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
      Γ ⊢ .pair a b ∶ .sigma q (some σ) A B⟩
  | fst {Γ : Ctx} {p A B : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ∶ .sigma q (some σ) A B], Γ ⊢ .fst p ∶ A⟩
  | snd {Γ : Ctx} {p A B : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ∶ .sigma q (some σ) A B], Γ ⊢ .snd p ∶ B.inst (.fst p)⟩
  | fstBeta {Γ : Ctx} {A B a b : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ .sigma q (some σ) A B ∶ .sort σ.sigma, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
      Γ ⊢ .fst (.pair a b) ⟶ a ∶ A⟩
  | sndBeta {Γ : Ctx} {A B a b : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ .sigma q (some σ) A B ∶ .sort σ.sigma, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
      Γ ⊢ .snd (.pair a b) ⟶ b ∶ B.inst a⟩
  | fstRed {Γ : Ctx} {p p' A B : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ⟶ p' ∶ .sigma q (some σ) A B], Γ ⊢ .fst p ⟶ .fst p' ∶ A⟩
  | sndRed {Γ : Ctx} {p p' A B : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ⟶ p' ∶ .sigma q (some σ) A B], Γ ⊢ .snd p ⟶ .snd p' ∶ B.inst (.fst p)⟩
  /-- η, as extensionality -/
  | eta {Γ : Ctx} {p A B p' : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ∶ .sigma q (some σ) A B, Γ ⊢ p' ∶ .sigma q (some σ) A B,
        Γ ⊢ .fst p ≡ .fst p' ∶ A, Γ ⊢ .snd p ≡ .snd p' ∶ B.inst (.fst p)],
      Γ ⊢ p ≡ p' ∶ .sigma q (some σ) A B⟩
  | cong {Γ : Ctx} {A A' B B' : Tm} {σ σ' : Sorts} {q : Q} : σ.dom.Equiv σ'.dom → σ.cod.Equiv σ'.cod →
      Sigma ⟨[Γ ⊢ A ∶ .sort σ.dom, Γ ⊢ A ≡ A' ∶ .sort σ.dom, (A :: Γ) ⊢ B ≡ B' ∶ .sort σ.cod],
        Γ ⊢ .sigma q (some σ) A B ≡ .sigma q (some σ') A' B' ∶ .sort σ.sigma⟩
  | fstCong {Γ : Ctx} {p p' A B : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ≡ p' ∶ .sigma q (some σ) A B], Γ ⊢ .fst p ≡ .fst p' ∶ A⟩
  | sndCong {Γ : Ctx} {p p' A B : Tm} {σ : Sorts} {q : Q} : Sigma ⟨[Γ ⊢ p ≡ p' ∶ .sigma q (some σ) A B], Γ ⊢ .snd p ≡ .snd p' ∶ B.inst (.fst p)⟩
  /-- an equation between pairs: the first components, and the second ones along a cast; a
  component's equation is `True` when its sort (as written in `σ`) is `0`, and then `ê` is
  `reflTy` if it is the first (the proof-component rule, as in both kernels) -/
  | eq {Γ : Ctx} {A B a b : Tm} {σ : Sorts} {q : Q} : σ.sigma.NeverZero →
      Sigma ⟨[Γ ⊢ .sigma q (some σ) A B ∶ .sort σ.sigma, Γ ⊢ a ∶ .sigma q (some σ) A B, Γ ⊢ b ∶ .sigma q (some σ) A B],
        Γ ⊢ .eq (.sigma q (some σ) A B) a b ⟶ .eqSigma σ A B a b ∶ .sort 0⟩
  | eqTyApart {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {σ₁ σ₂ : Sorts} {q q' : Q} : σ₁.sigma.NeverZero → σ₂.sigma.NeverZero → q ≠ q' →
      Sigma ⟨[Γ ⊢ .sigma q (some σ₁) A₁ B₁ ∶ .sort σ₁.sigma, Γ ⊢ .sigma q' (some σ₂) A₂ B₂ ∶ .sort σ₂.sigma],
        Γ ⊢ .eqTy (.sigma q (some σ₁) A₁ B₁) (.sigma q' (some σ₂) A₂ B₂) ⟶ .False' ∶ .sort 0⟩
  /-- as for `Π`: the components pairwise in one sort -/
  | cast {Γ : Ctx} {A₁ B₁ A₂ B₂ e t : Tm} {σ₁ σ₂ : Sorts} {q : Q} : σ₁.sigma.NeverZero → σ₂.sigma.NeverZero →
      σ₁.dom.Equiv σ₂.dom → σ₁.cod.Equiv σ₂.cod →
      Sigma ⟨[Γ ⊢ .sigma q (some σ₁) A₁ B₁ ∶ .sort σ₁.sigma, Γ ⊢ .sigma q (some σ₂) A₂ B₂ ∶ .sort σ₂.sigma,
          Γ ⊢ A₁ ∶ .sort σ₁.dom, Γ ⊢ A₂ ∶ .sort σ₁.dom, (A₁ :: Γ) ⊢ B₁ ∶ .sort σ₁.cod, (A₂ :: Γ) ⊢ B₂ ∶ .sort σ₁.cod,
          Γ ⊢ e ∶ .eqTy (.sigma q (some σ₁) A₁ B₁) (.sigma q (some σ₂) A₂ B₂), Γ ⊢ t ∶ .sigma q (some σ₁) A₁ B₁],
        Γ ⊢ .cast (.sigma q (some σ₁) A₁ B₁) (.sigma q (some σ₂) A₂ B₂) e t ⟶ .castSigma A₁ B₁ A₂ B₂ e t
          ∶ .sigma q (some σ₂) A₂ B₂⟩

end WizMeta.Spec
