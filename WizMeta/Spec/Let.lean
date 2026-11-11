import WizMeta.Spec.Rule

/-!
# `let` and ascription

`let` is transparent: its body is typed with the variable replaced by the value, which is
what the kernels' "the body sees `x := v`" amounts to. Both formers reduce away.
-/

namespace WizMeta.Spec

inductive Let : Rules
  | letE {Γ : Ctx} {A v B b : Tm} {l : Lvl} {q : Q} : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ v ∶ A, Γ ⊢ b.inst v ∶ B], Γ ⊢ .letE q A v b ∶ B⟩
  | zeta {Γ : Ctx} {A v B b : Tm} {l : Lvl} {q : Q} : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ v ∶ A, Γ ⊢ b.inst v ∶ B], Γ ⊢ .letE q A v b ⟶ b.inst v ∶ B⟩
  | ann {Γ : Ctx} {A t : Tm} {l : Lvl} : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ t ∶ A], Γ ⊢ .ann t A ∶ A⟩
  | annRed {Γ : Ctx} {A t : Tm} {l : Lvl} : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ t ∶ A], Γ ⊢ .ann t A ⟶ t ∶ A⟩

end WizMeta.Spec
