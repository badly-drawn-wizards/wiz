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

inductive ULift : Rules
  | form {Γ : Ctx} {A : Tm} {k l : Lvl} : (Lvl.max k l).Equiv l → ULift ⟨[Γ ⊢ A ∶ .sort k], Γ ⊢ .ulift l A ∶ .sort l⟩
  | up {Γ : Ctx} {A a : Tm} {l : Lvl} : ULift ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .up a ∶ .ulift l A⟩
  | down {Γ : Ctx} {t A : Tm} {l : Lvl} : ULift ⟨[Γ ⊢ t ∶ .ulift l A], Γ ⊢ .down t ∶ A⟩
  | beta {Γ : Ctx} {A a : Tm} {l : Lvl} : ULift ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .down (.up a) ⟶ a ∶ A⟩
  | downRed {Γ : Ctx} {t t' A : Tm} {l : Lvl} : ULift ⟨[Γ ⊢ t ⟶ t' ∶ .ulift l A], Γ ⊢ .down t ⟶ .down t' ∶ A⟩
  | eta {Γ : Ctx} {t A t' : Tm} {l : Lvl} : ULift ⟨[Γ ⊢ t ∶ .ulift l A, Γ ⊢ t' ∶ .ulift l A, Γ ⊢ .down t ≡ .down t' ∶ A], Γ ⊢ t ≡ t' ∶ .ulift l A⟩
  | cong {Γ : Ctx} {A A' : Tm} {l k l' : Lvl} : l.Equiv l' → ULift ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ A ≡ A' ∶ .sort k], Γ ⊢ .ulift l A ≡ .ulift l' A' ∶ .sort l⟩
  | downCong {Γ : Ctx} {t t' A : Tm} {l : Lvl} : ULift ⟨[Γ ⊢ t ≡ t' ∶ .ulift l A], Γ ⊢ .down t ≡ .down t' ∶ A⟩
  /-- boxed proofs are all equal -/
  | eqProp {Γ : Ctx} {A a b : Tm} {k l : Lvl} : l.NeverZero → k.IsZero →
      ULift ⟨[Γ ⊢ A ∶ .sort k, Γ ⊢ a ∶ .ulift l A, Γ ⊢ b ∶ .ulift l A], Γ ⊢ .eq (.ulift l A) a b ⟶ .True' ∶ .sort 0⟩
  | eq {Γ : Ctx} {A a b : Tm} {k l : Lvl} : l.NeverZero → k.NeverZero →
      ULift ⟨[Γ ⊢ A ∶ .sort k, Γ ⊢ a ∶ .ulift l A, Γ ⊢ b ∶ .ulift l A],
        Γ ⊢ .eq (.ulift l A) a b ⟶ .eq A (.down a) (.down b) ∶ .sort 0⟩
  | eqTy {Γ : Ctx} {A B : Tm} {u w : Lvl} : u.NeverZero → u.Equiv w →
      ULift ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w], Γ ⊢ .eqTy (.ulift u A) (.ulift w B) ⟶ .eqTy A B ∶ .sort 0⟩
  | eqTyApart {Γ : Ctx} {A B : Tm} {u w : Lvl} {m n : Nat} : u.toNat? = some (m + 1) → w.toNat? = some (n + 1) → m ≠ n →
      ULift ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w], Γ ⊢ .eqTy (.ulift u A) (.ulift w B) ⟶ .False' ∶ .sort 0⟩
  | cast {Γ : Ctx} {A B e t : Tm} {u w : Lvl} : u.NeverZero → u.Equiv w →
      ULift ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w, Γ ⊢ e ∶ .eqTy (.ulift u A) (.ulift w B),
          Γ ⊢ t ∶ .ulift u A],
        Γ ⊢ .cast (.ulift u A) (.ulift w B) e t ⟶ .up (.cast A B e (.down t)) ∶ .ulift w B⟩
  | qty {Γ : Ctx} : ULift ⟨[.wf Γ], Γ ⊢ .qty ∶ .sort 1⟩
  | qlit {Γ : Ctx} {q : Q} : ULift ⟨[.wf Γ], Γ ⊢ .qlit q ∶ .qty⟩

end WizMeta.Spec
