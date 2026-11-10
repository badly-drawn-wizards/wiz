import WizMeta.Spec.Rule

/-!
# `let` and ascription

`let` is transparent: its body is typed with the variable replaced by the value, which is
what the kernels' "the body sees `x := v`" amounts to. Both formers reduce away.
-/

namespace WizMeta.Spec
set_option autoImplicit true

inductive Let : Rules
  | letE : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ v ∶ A, Γ ⊢ b.inst v ∶ B], Γ ⊢ .letE q A v b ∶ B⟩
  | zeta : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ v ∶ A, Γ ⊢ b.inst v ∶ B], Γ ⊢ .letE q A v b ⟶ b.inst v ∶ B⟩
  | ann : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ t ∶ A], Γ ⊢ .ann t A ∶ A⟩
  | annRed : Let ⟨[Γ ⊢ A ∶ .sort l, Γ ⊢ t ∶ A], Γ ⊢ .ann t A ⟶ t ∶ A⟩

end WizMeta.Spec
