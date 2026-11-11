import WizMeta.Spec.Rule

/-!
# Structural rules, universes, proof irrelevance

`Sort l : Sort (l+1)`, non-cumulative. Level side conditions are semantic (`Lvl.Equiv`,
`Lvl.IsZero`: under every assignment of the level parameters).
-/

namespace WizMeta.Spec

inductive Core : Rules
  | wfNil : Core ⟨[], .wf []⟩
  | wfCons {Γ : Ctx} {A : Tm} {l : Lvl} : Core ⟨[.wf Γ, Γ ⊢ A ∶ .sort l], .wf (A :: Γ)⟩
  | var {Γ : Ctx} {A : Tm} {i : Nat} : Γ.lookup i = some A → Core ⟨[.wf Γ], Γ ⊢ .var i ∶ A⟩
  | sort {Γ : Ctx} {l : Lvl} : Core ⟨[.wf Γ], Γ ⊢ .sort l ∶ .sort l.succ⟩
  | sortCong {Γ : Ctx} {l l' : Lvl} : l.Equiv l' → Core ⟨[.wf Γ], Γ ⊢ .sort l ≡ .sort l' ∶ .sort l.succ⟩
  /-- conversion -/
  | conv {Γ : Ctx} {t A B : Tm} {l : Lvl} : Core ⟨[Γ ⊢ t ∶ A, Γ ⊢ A ≡ B ∶ .sort l], Γ ⊢ t ∶ B⟩
  | eqConv {Γ : Ctx} {t u A B : Tm} {l : Lvl} : Core ⟨[Γ ⊢ t ≡ u ∶ A, Γ ⊢ A ≡ B ∶ .sort l], Γ ⊢ t ≡ u ∶ B⟩
  | redConv {Γ : Ctx} {t u A B : Tm} {l : Lvl} : Core ⟨[Γ ⊢ t ⟶ u ∶ A, Γ ⊢ A ≡ B ∶ .sort l], Γ ⊢ t ⟶ u ∶ B⟩
  | refl {Γ : Ctx} {t A : Tm} : Core ⟨[Γ ⊢ t ∶ A], Γ ⊢ t ≡ t ∶ A⟩
  | symm {Γ : Ctx} {t u A : Tm} : Core ⟨[Γ ⊢ t ≡ u ∶ A], Γ ⊢ u ≡ t ∶ A⟩
  | trans {Γ : Ctx} {t u A w : Tm} : Core ⟨[Γ ⊢ t ≡ u ∶ A, Γ ⊢ u ≡ w ∶ A], Γ ⊢ t ≡ w ∶ A⟩
  /-- a reduction step is a conversion -/
  | redEq {Γ : Ctx} {t u A : Tm} : Core ⟨[Γ ⊢ t ⟶ u ∶ A], Γ ⊢ t ≡ u ∶ A⟩
  /-- definitional proof irrelevance: at a proposition any two terms are convertible -/
  | irrel {Γ : Ctx} {A t u : Tm} {l : Lvl} : l.IsZero → Core ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ t ∶ A, Γ ⊢ u ∶ A], Γ ⊢ t ≡ u ∶ A⟩
  /-- equality of universes: propext at `Prop`, type equality above it -/
  | eqProp {Γ : Ctx} {a b : Tm} {l : Lvl} : l.IsZero →
      Core ⟨[Γ ⊢ a ∶ .sort l, Γ ⊢ b ∶ .sort l], Γ ⊢ .eq (.sort l) a b ⟶ .iff a b ∶ .sort 0⟩
  | eqType {Γ : Ctx} {a b : Tm} {l : Lvl} : l.NeverZero →
      Core ⟨[Γ ⊢ a ∶ .sort l, Γ ⊢ b ∶ .sort l], Γ ⊢ .eq (.sort l) a b ⟶ .eqTy a b ∶ .sort 0⟩
  | eqTySort {Γ : Ctx} {u w : Lvl} : u.Equiv w → Core ⟨[.wf Γ], Γ ⊢ .eqTy (.sort u) (.sort w) ⟶ .True' ∶ .sort 0⟩
  /-- two different closed levels: the answer must not change under a level substitution -/
  | eqTySortApart {Γ : Ctx} {u w : Lvl} {m n : Nat} : u.toNat? = some m → w.toNat? = some n → m ≠ n →
      Core ⟨[.wf Γ], Γ ⊢ .eqTy (.sort u) (.sort w) ⟶ .False' ∶ .sort 0⟩
  /-- the identity cast at a universe -/
  | castSort {Γ : Ctx} {e t : Tm} {u w : Lvl} : u.Equiv w →
      Core ⟨[Γ ⊢ e ∶ .eqTy (.sort u) (.sort w), Γ ⊢ t ∶ .sort u], Γ ⊢ .cast (.sort u) (.sort w) e t ⟶ t ∶ .sort w⟩

end WizMeta.Spec
