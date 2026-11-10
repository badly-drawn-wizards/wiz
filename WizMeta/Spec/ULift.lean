import WizMeta.Spec.Rule

/-!
# ULift, and the type of quantities

`ULift.{l} A : Sort l` for `A : Sort k`, `k ≤ l`: a one-field record with η. Its
observational rules go through the field. A lifted proposition above `Prop` is not a
proposition, but has one inhabitant up to conversion (η and irrelevance), so equations
at it are `True`.

The rules that choose by a level (`ULift.{u} A ≡ ULift.{w} B`, the cast) require `u` to be
never `0`, not merely "not known to be `0`", so the choice survives a level substitution
(at `u = 0` both sides are propositions and `Eq.eqTyProps` applies). The kernels answer
`A ≡ B` for a level parameter `u` (model-memo row T10).

`Qty` is the type of the three quantity literals. Binders carry labels, not terms; `Qty`
exists because the methods of `Desc.elim` are generic in a field's quantity.
-/

namespace WizMeta.Spec
set_option autoImplicit true

inductive ULift : Rules
  | form : (Lvl.max k l).Equiv l → ULift ⟨[Γ ⊢ A ∶ .sort k], Γ ⊢ .ulift l A ∶ .sort l⟩
  | up : ULift ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .up a ∶ .ulift l A⟩
  | down : ULift ⟨[Γ ⊢ t ∶ .ulift l A], Γ ⊢ .down t ∶ A⟩
  | beta : ULift ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .down (.up a) ⟶ a ∶ A⟩
  | downRed : ULift ⟨[Γ ⊢ t ⟶ t' ∶ .ulift l A], Γ ⊢ .down t ⟶ .down t' ∶ A⟩
  | eta : ULift ⟨[Γ ⊢ t ∶ .ulift l A, Γ ⊢ t' ∶ .ulift l A, Γ ⊢ .down t ≡ .down t' ∶ A], Γ ⊢ t ≡ t' ∶ .ulift l A⟩
  | cong : l.Equiv l' → ULift ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ A ≡ A' ∶ .sort k], Γ ⊢ .ulift l A ≡ .ulift l' A' ∶ .sort l⟩
  | downCong : ULift ⟨[Γ ⊢ t ≡ t' ∶ .ulift l A], Γ ⊢ .down t ≡ .down t' ∶ A⟩
  /-- boxed proofs are all equal -/
  | eqProp : l.NeverZero → k.IsZero →
      ULift ⟨[Γ ⊢ A ∶ .sort k, Γ ⊢ a ∶ .ulift l A, Γ ⊢ b ∶ .ulift l A], Γ ⊢ .eq (.ulift l A) a b ⟶ .True' ∶ .sort 0⟩
  | eq : l.NeverZero → k.NeverZero →
      ULift ⟨[Γ ⊢ A ∶ .sort k, Γ ⊢ a ∶ .ulift l A, Γ ⊢ b ∶ .ulift l A],
        Γ ⊢ .eq (.ulift l A) a b ⟶ .eq A (.down a) (.down b) ∶ .sort 0⟩
  | eqTy : u.NeverZero → u.Equiv w →
      ULift ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w], Γ ⊢ .eqTy (.ulift u A) (.ulift w B) ⟶ .eqTy A B ∶ .sort 0⟩
  | eqTyApart : u.toNat? = some (m + 1) → w.toNat? = some (n + 1) → m ≠ n →
      ULift ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w], Γ ⊢ .eqTy (.ulift u A) (.ulift w B) ⟶ .False' ∶ .sort 0⟩
  | cast : u.NeverZero → u.Equiv w →
      ULift ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w, Γ ⊢ e ∶ .eqTy (.ulift u A) (.ulift w B),
          Γ ⊢ t ∶ .ulift u A],
        Γ ⊢ .cast (.ulift u A) (.ulift w B) e t ⟶ .up (.cast A B e (.down t)) ∶ .ulift w B⟩
  | qty : ULift ⟨[.wf Γ], Γ ⊢ .qty ∶ .sort 1⟩
  | qlit : ULift ⟨[.wf Γ], Γ ⊢ .qlit q ∶ .qty⟩

end WizMeta.Spec
