import WizMeta.Spec.Rule

/-!
# Σ

`(q x : A) × B` in `Sort s`, `s ≡ max i j` (so a `Σ` of two propositions is one). Pairs,
projections, β as reductions, η as a conversion rule. No `split` (it is `Σ`-η plus `let`).

The rule for an equation between two such types with the same quantity is in
`EqTyCross.lean` / `EqTyLevelled.lean` (two variants).
-/

namespace WizMeta.Spec

inductive Sigma : Rules
  | form {Γ : Ctx} {A B : Tm} {i j s : Lvl} {q : Q} : s.Equiv (.max i j) →
      Sigma ⟨[Γ ⊢ A ∶ .sort i, (A :: Γ) ⊢ B ∶ .sort j], Γ ⊢ .sigma q (some s) A B ∶ .sort s⟩
  | pair {Γ : Ctx} {A B a b : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ .sigma q (some s) A B ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
      Γ ⊢ .pair a b ∶ .sigma q (some s) A B⟩
  | fst {Γ : Ctx} {p A B : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ∶ .sigma q (some s) A B], Γ ⊢ .fst p ∶ A⟩
  | snd {Γ : Ctx} {p A B : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ∶ .sigma q (some s) A B], Γ ⊢ .snd p ∶ B.inst (.fst p)⟩
  | fstBeta {Γ : Ctx} {A B a b : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ .sigma q (some s) A B ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
      Γ ⊢ .fst (.pair a b) ⟶ a ∶ A⟩
  | sndBeta {Γ : Ctx} {A B a b : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ .sigma q (some s) A B ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
      Γ ⊢ .snd (.pair a b) ⟶ b ∶ B.inst a⟩
  | fstRed {Γ : Ctx} {p p' A B : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ⟶ p' ∶ .sigma q (some s) A B], Γ ⊢ .fst p ⟶ .fst p' ∶ A⟩
  | sndRed {Γ : Ctx} {p p' A B : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ⟶ p' ∶ .sigma q (some s) A B], Γ ⊢ .snd p ⟶ .snd p' ∶ B.inst (.fst p)⟩
  /-- η, as extensionality -/
  | eta {Γ : Ctx} {p A B p' : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ∶ .sigma q (some s) A B, Γ ⊢ p' ∶ .sigma q (some s) A B,
        Γ ⊢ .fst p ≡ .fst p' ∶ A, Γ ⊢ .snd p ≡ .snd p' ∶ B.inst (.fst p)],
      Γ ⊢ p ≡ p' ∶ .sigma q (some s) A B⟩
  | cong {Γ : Ctx} {A A' B B' : Tm} {i j s s' : Lvl} {q : Q} : s.Equiv (.max i j) → s'.Equiv (.max i j) →
      Sigma ⟨[Γ ⊢ A ≡ A' ∶ .sort i, (A :: Γ) ⊢ B ≡ B' ∶ .sort j],
        Γ ⊢ .sigma q (some s) A B ≡ .sigma q (some s') A' B' ∶ .sort s⟩
  | fstCong {Γ : Ctx} {p p' A B : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ≡ p' ∶ .sigma q (some s) A B], Γ ⊢ .fst p ≡ .fst p' ∶ A⟩
  | sndCong {Γ : Ctx} {p p' A B : Tm} {s : Lvl} {q : Q} : Sigma ⟨[Γ ⊢ p ≡ p' ∶ .sigma q (some s) A B], Γ ⊢ .snd p ≡ .snd p' ∶ B.inst (.fst p)⟩
  /-- an equation between pairs: the first components, and the second ones along a cast -/
  | eq {Γ : Ctx} {A B a b : Tm} {s : Lvl} {q : Q} : s.NeverZero →
      Sigma ⟨[Γ ⊢ .sigma q (some s) A B ∶ .sort s, Γ ⊢ a ∶ .sigma q (some s) A B, Γ ⊢ b ∶ .sigma q (some s) A B],
        Γ ⊢ .eq (.sigma q (some s) A B) a b ⟶ .eqSigma A B a b ∶ .sort 0⟩
  | eqTyApart {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Lvl} {q q' : Q} : s₁.NeverZero → s₂.NeverZero → q ≠ q' →
      Sigma ⟨[Γ ⊢ .sigma q (some s₁) A₁ B₁ ∶ .sort s₁, Γ ⊢ .sigma q' (some s₂) A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.sigma q (some s₁) A₁ B₁) (.sigma q' (some s₂) A₂ B₂) ⟶ .False' ∶ .sort 0⟩
  | cast {Γ : Ctx} {A₁ B₁ A₂ B₂ e t : Tm} {s₁ s₂ : Lvl} {q : Q} : s₁.NeverZero → s₂.NeverZero →
      Sigma ⟨[Γ ⊢ .sigma q (some s₁) A₁ B₁ ∶ .sort s₁, Γ ⊢ .sigma q (some s₂) A₂ B₂ ∶ .sort s₂,
          Γ ⊢ e ∶ .eqTy (.sigma q (some s₁) A₁ B₁) (.sigma q (some s₂) A₂ B₂), Γ ⊢ t ∶ .sigma q (some s₁) A₁ B₁],
        Γ ⊢ .cast (.sigma q (some s₁) A₁ B₁) (.sigma q (some s₂) A₂ B₂) e t ⟶ .castSigma A₁ B₁ A₂ B₂ e t
          ∶ .sigma q (some s₂) A₂ B₂⟩

end WizMeta.Spec
