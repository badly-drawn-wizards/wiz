import WizMeta.Spec.Rule

/-!
# Unit and Empty

`Unit_l` and `Empty_l` at every level; `True = Unit_0`, `False = Empty_0`. η for `Unit`
(all elements are convertible). `absurd` never computes.
-/

namespace WizMeta.Spec

inductive Unit : Rules
  | form {Γ : Ctx} {l : Lvl} : Unit ⟨[.wf Γ], Γ ⊢ .unit l ∶ .sort l⟩
  | tt {Γ : Ctx} {l : Lvl} : Unit ⟨[.wf Γ], Γ ⊢ .tt ∶ .unit l⟩
  | eta {Γ : Ctx} {t u : Tm} {l : Lvl} : Unit ⟨[Γ ⊢ t ∶ .unit l, Γ ⊢ u ∶ .unit l], Γ ⊢ t ≡ u ∶ .unit l⟩
  | cong {Γ : Ctx} {l l' : Lvl} : l.Equiv l' → Unit ⟨[.wf Γ], Γ ⊢ .unit l ≡ .unit l' ∶ .sort l⟩
  | eq {Γ : Ctx} {a b : Tm} {l : Lvl} : l.NeverZero → Unit ⟨[Γ ⊢ a ∶ .unit l, Γ ⊢ b ∶ .unit l], Γ ⊢ .eq (.unit l) a b ⟶ .True' ∶ .sort 0⟩
  | eqTy {Γ : Ctx} {u w : Lvl} : u.NeverZero → w.NeverZero → u.Equiv w →
      Unit ⟨[.wf Γ], Γ ⊢ .eqTy (.unit u) (.unit w) ⟶ .True' ∶ .sort 0⟩
  | eqTyApart {Γ : Ctx} {u w : Lvl} {m n : Nat} : u.toNat? = some (m + 1) → w.toNat? = some (n + 1) → m ≠ n →
      Unit ⟨[.wf Γ], Γ ⊢ .eqTy (.unit u) (.unit w) ⟶ .False' ∶ .sort 0⟩
  | cast {Γ : Ctx} {e t : Tm} {u w : Lvl} : u.NeverZero → u.Equiv w →
      Unit ⟨[Γ ⊢ e ∶ .eqTy (.unit u) (.unit w), Γ ⊢ t ∶ .unit u], Γ ⊢ .cast (.unit u) (.unit w) e t ⟶ .tt ∶ .unit w⟩

inductive Empty : Rules
  | form {Γ : Ctx} {l : Lvl} : Empty ⟨[.wf Γ], Γ ⊢ .empty l ∶ .sort l⟩
  | absurd {Γ : Ctx} {M t : Tm} {k l : Lvl} : Empty ⟨[Γ ⊢ M ∶ .sort k, Γ ⊢ t ∶ .empty l], Γ ⊢ .absurd M t ∶ M⟩
  | cong {Γ : Ctx} {l l' : Lvl} : l.Equiv l' → Empty ⟨[.wf Γ], Γ ⊢ .empty l ≡ .empty l' ∶ .sort l⟩
  | absurdCong {Γ : Ctx} {M M' t t' : Tm} {k l : Lvl} : Empty ⟨[Γ ⊢ M ≡ M' ∶ .sort k, Γ ⊢ t ≡ t' ∶ .empty l], Γ ⊢ .absurd M t ≡ .absurd M' t' ∶ M⟩
  | eq {Γ : Ctx} {a b : Tm} {l : Lvl} : l.NeverZero → Empty ⟨[Γ ⊢ a ∶ .empty l, Γ ⊢ b ∶ .empty l], Γ ⊢ .eq (.empty l) a b ⟶ .True' ∶ .sort 0⟩
  | eqTy {Γ : Ctx} {u w : Lvl} : u.NeverZero → w.NeverZero → u.Equiv w →
      Empty ⟨[.wf Γ], Γ ⊢ .eqTy (.empty u) (.empty w) ⟶ .True' ∶ .sort 0⟩
  | eqTyApart {Γ : Ctx} {u w : Lvl} {m n : Nat} : u.toNat? = some (m + 1) → w.toNat? = some (n + 1) → m ≠ n →
      Empty ⟨[.wf Γ], Γ ⊢ .eqTy (.empty u) (.empty w) ⟶ .False' ∶ .sort 0⟩
  | cast {Γ : Ctx} {e t : Tm} {u w : Lvl} : u.NeverZero → u.Equiv w →
      Empty ⟨[Γ ⊢ e ∶ .eqTy (.empty u) (.empty w), Γ ⊢ t ∶ .empty u], Γ ⊢ .cast (.empty u) (.empty w) e t ⟶ t ∶ .empty w⟩

end WizMeta.Spec
