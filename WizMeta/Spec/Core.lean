import WizMeta.Spec.Rule

/-!
# Structural rules, universes, proof irrelevance

`Sort l : Sort (l+1)`, non-cumulative. Level side conditions are semantic (`Lvl.Equiv`,
`Lvl.IsZero`: under every assignment of the level parameters).
-/

namespace WizMeta.Spec
set_option autoImplicit true

inductive Core : Rules
  | wfNil : Core ⟨[], .wf []⟩
  | wfCons : Core ⟨[.wf Γ, Γ ⊢ A ∶ .sort l], .wf (A :: Γ)⟩
  | var : Γ.lookup i = some A → Core ⟨[.wf Γ], Γ ⊢ .var i ∶ A⟩
  | sort : Core ⟨[.wf Γ], Γ ⊢ .sort l ∶ .sort l.succ⟩
  | sortCong : l.Equiv l' → Core ⟨[.wf Γ], Γ ⊢ .sort l ≡ .sort l' ∶ .sort l.succ⟩
  /-- conversion -/
  | conv : Core ⟨[Γ ⊢ t ∶ A, Γ ⊢ A ≡ B ∶ .sort l], Γ ⊢ t ∶ B⟩
  | eqConv : Core ⟨[Γ ⊢ t ≡ u ∶ A, Γ ⊢ A ≡ B ∶ .sort l], Γ ⊢ t ≡ u ∶ B⟩
  | redConv : Core ⟨[Γ ⊢ t ⟶ u ∶ A, Γ ⊢ A ≡ B ∶ .sort l], Γ ⊢ t ⟶ u ∶ B⟩
  | refl : Core ⟨[Γ ⊢ t ∶ A], Γ ⊢ t ≡ t ∶ A⟩
  | symm : Core ⟨[Γ ⊢ t ≡ u ∶ A], Γ ⊢ u ≡ t ∶ A⟩
  | trans : Core ⟨[Γ ⊢ t ≡ u ∶ A, Γ ⊢ u ≡ w ∶ A], Γ ⊢ t ≡ w ∶ A⟩
  /-- a reduction step is a conversion -/
  | redEq : Core ⟨[Γ ⊢ t ⟶ u ∶ A], Γ ⊢ t ≡ u ∶ A⟩
  /-- definitional proof irrelevance: at a proposition any two terms are convertible -/
  | irrel : l.IsZero → Core ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ t ∶ A, Γ ⊢ u ∶ A], Γ ⊢ t ≡ u ∶ A⟩
  /-- equality of universes: propext at `Prop`, type equality above it -/
  | eqProp : l.IsZero →
      Core ⟨[Γ ⊢ a ∶ .sort l, Γ ⊢ b ∶ .sort l], Γ ⊢ .eq (.sort l) a b ⟶ .iff a b ∶ .sort 0⟩
  | eqType : l.NeverZero →
      Core ⟨[Γ ⊢ a ∶ .sort l, Γ ⊢ b ∶ .sort l], Γ ⊢ .eq (.sort l) a b ⟶ .eqTy a b ∶ .sort 0⟩
  | eqTySort : u.Equiv w → Core ⟨[.wf Γ], Γ ⊢ .eqTy (.sort u) (.sort w) ⟶ .True' ∶ .sort 0⟩
  /-- two different closed levels: the answer must not change under a level substitution -/
  | eqTySortApart : u.toNat? = some m → w.toNat? = some n → m ≠ n →
      Core ⟨[.wf Γ], Γ ⊢ .eqTy (.sort u) (.sort w) ⟶ .False' ∶ .sort 0⟩
  /-- the identity cast at a universe -/
  | castSort : u.Equiv w →
      Core ⟨[Γ ⊢ e ∶ .eqTy (.sort u) (.sort w), Γ ⊢ t ∶ .sort u], Γ ⊢ .cast (.sort u) (.sort w) e t ⟶ t ∶ .sort w⟩

end WizMeta.Spec
