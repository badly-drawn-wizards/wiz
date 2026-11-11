import WizMeta.Spec.Rule

/-!
# μ, constructors, induction

`μ.{l} I D i : Sort (l+1)` (no inductive propositions; no sizes: this is `μ^∞`).

* **The level premise on the eliminator** (audit F3): `ind` requires `I : Sort (l+1)`,
  as the formers do, so the types it builds are types the formers accept.
* **Equations between constructors** are in three variant files, `PayloadKernel.lean`,
  `PayloadStuck.lean`, `PayloadUniform.lean`: an open design question.

Not here: `μ I D i ≡ μ I' D' i'` and casts at `μ` (PR #40's rules by codes are not on
master; master's rule compares the two families syntactically, which is not a rule the
spec can state). In the spec both are stuck, and T1 identifies a cast between
convertible inert `μ` types with its argument.
-/

namespace WizMeta.Spec

inductive Mu : Rules
  | form {Γ : Ctx} {I D i : Tm} {l : Lvl} : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ i ∶ I], Γ ⊢ .mu l I D i ∶ .sort l.succ⟩
  | con {Γ : Ctx} {I D i x : Tm} {l : Lvl} : Mu ⟨[Γ ⊢ .mu l I D i ∶ .sort l.succ, Γ ⊢ x ∶ .interp l I D (.muFamily l I D) i],
      Γ ⊢ .con x ∶ .mu l I D i⟩
  | ind {Γ : Ctx} {I D P m i x : Tm} {l v : Lvl} : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ P ∶ .indMotiveTy l v I D,
        Γ ⊢ m ∶ .indMethodTy l v I D P, Γ ⊢ i ∶ I, Γ ⊢ x ∶ .mu l I D i],
      Γ ⊢ .ind l I D v P m i x ∶ .apps P [i, x]⟩
  | iota {Γ : Ctx} {I D P m i xs : Tm} {l v : Lvl} : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ P ∶ .indMotiveTy l v I D,
        Γ ⊢ m ∶ .indMethodTy l v I D P, Γ ⊢ i ∶ I, Γ ⊢ .con xs ∶ .mu l I D i],
      Γ ⊢ .ind l I D v P m i (.con xs) ⟶ .indCon l v I D P m i xs ∶ .apps P [i, .con xs]⟩
  | indRed {Γ : Ctx} {I D P m i x x' : Tm} {l v : Lvl} : Mu ⟨[Γ ⊢ I ∶ .sort l.succ, Γ ⊢ D ∶ .desc l I, Γ ⊢ P ∶ .indMotiveTy l v I D,
        Γ ⊢ m ∶ .indMethodTy l v I D P, Γ ⊢ i ∶ I, Γ ⊢ x ⟶ x' ∶ .mu l I D i],
      Γ ⊢ .ind l I D v P m i x ⟶ .ind l I D v P m i x' ∶ .apps P [i, x]⟩
  | cong {Γ : Ctx} {I I' D D' i i' : Tm} {l l' : Lvl} : l.Equiv l' →
      Mu ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ i ≡ i' ∶ I],
        Γ ⊢ .mu l I D i ≡ .mu l' I' D' i' ∶ .sort l.succ⟩
  | conCong {Γ : Ctx} {I D i x y : Tm} {l : Lvl} : Mu ⟨[Γ ⊢ .mu l I D i ∶ .sort l.succ, Γ ⊢ x ≡ y ∶ .interp l I D (.muFamily l I D) i],
      Γ ⊢ .con x ≡ .con y ∶ .mu l I D i⟩
  | indCong {Γ : Ctx} {I I' D D' P P' m m' i i' x x' : Tm} {l v l' v' : Lvl} : l.Equiv l' → v.Equiv v' →
      Mu ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ P ≡ P' ∶ .indMotiveTy l v I D,
          Γ ⊢ m ≡ m' ∶ .indMethodTy l v I D P, Γ ⊢ i ≡ i' ∶ I, Γ ⊢ x ≡ x' ∶ .mu l I D i],
        Γ ⊢ .ind l I D v P m i x ≡ .ind l' I' D' v' P' m' i' x' ∶ .apps P [i, x]⟩

end WizMeta.Spec
