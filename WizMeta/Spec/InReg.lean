import WizMeta.Spec.Rule

/-!
# T1: regularity at inert types, as a conversion rule

    A inert     Γ ⊢ A ≡ B     Γ ⊢ e : A ≡ B     Γ ⊢ t : A
    ───────────────────────────────────────────────────────  InReg_conv
    Γ ⊢ cast A B e t ≡ t : B

[PLT25]'s Cast-Refl restricted to inert `A`. It is a rule of conversion, not a reduction,
and its side condition is conversion (no syntactic comparison, no "ground" test).

Inert types are first-order data: `Enum`, `Unit` above `Prop`, lifts and `Σ`s of inert
types that are not propositions, and `μ` types whose index type and fields are inert
(`rec` fields; `arg` at inert types; no `hrec`). Inertness is a judgment, closed under
conversion; with mandatory sorts it reads no annotation that conversion ignores.

Without `μ` (T1 as a fragment) every cast between convertible inert types already
computes, so the rule adds no equation there; it matters from T2 on (`Fin n`).
-/

namespace WizMeta.Spec

/-- `inertD` of `D tag` for every tag. -/
def tagPrems (Γ : Ctx) (l : Lvl) (I D : Tm) (k : Nat) (mk : Tm → Tm) : List Jdg :=
  (List.range k).map fun a => .inertD Γ l I (.app D (mk (.tag k a)))

inductive InReg : Rules
  | castRefl {Γ : Ctx} {A B e t : Tm} {l : Lvl} : InReg ⟨[.inert Γ A, Γ ⊢ A ≡ B ∶ .sort l, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A], Γ ⊢ .cast A B e t ≡ t ∶ B⟩
  | conv {Γ : Ctx} {A A' : Tm} {l : Lvl} : InReg ⟨[.inert Γ A, Γ ⊢ A ≡ A' ∶ .sort l], .inert Γ A'⟩
  | enum {Γ : Ctx} {n : Nat} : InReg ⟨[.wf Γ], .inert Γ (.enum n)⟩
  | unit {Γ : Ctx} {l : Lvl} : l.NeverZero → InReg ⟨[.wf Γ], .inert Γ (.unit l)⟩
  | ulift {Γ : Ctx} {A : Tm} {l : Lvl} : l.NeverZero → InReg ⟨[Γ ⊢ .ulift l A ∶ .sort l, .inert Γ A], .inert Γ (.ulift l A)⟩
  | sigma {Γ : Ctx} {A B : Tm} {s : Lvl} {q : Q} : s.NeverZero →
      InReg ⟨[Γ ⊢ .sigma q (some s) A B ∶ .sort s, .inert Γ A, .inert (A :: Γ) B], .inert Γ (.sigma q (some s) A B)⟩
  | mu {Γ : Ctx} {I D i : Tm} {l : Lvl} : InReg ⟨[Γ ⊢ .mu l I D i ∶ .sort l.succ, .inert Γ I, .inertD Γ l I D], .inert Γ (.mu l I D i)⟩
  | descConv {Γ : Ctx} {I D D' : Tm} {l : Lvl} : InReg ⟨[.inertD Γ l I D, Γ ⊢ D ≡ D' ∶ .desc l I], .inertD Γ l I D'⟩
  | ret {Γ : Ctx} {j I : Tm} {l : Lvl} : InReg ⟨[Γ ⊢ .dret j ∶ .desc l I], .inertD Γ l I (.dret j)⟩
  | drec {Γ : Ctx} {j I D q : Tm} {l : Lvl} : InReg ⟨[Γ ⊢ j ∶ I, .inertD Γ l I D], .inertD Γ l I (.drec q j D)⟩
  /-- a tag field: tag by tag -/
  | argTag {Γ : Ctx} {q D I : Tm} {l : Lvl} {k : Nat} : InReg ⟨(Γ ⊢ .darg q (.enum k) D ∶ .desc l I) :: tagPrems Γ l I D k id,
      .inertD Γ l I (.darg q (.enum k) D)⟩
  | argTagLifted {Γ : Ctx} {q D I : Tm} {u l : Lvl} {k : Nat} : InReg ⟨(Γ ⊢ .darg q (.ulift u (.enum k)) D ∶ .desc l I) :: tagPrems Γ l I D k .up,
      .inertD Γ l I (.darg q (.ulift u (.enum k)) D)⟩
  /-- any other inert field: under a variable -/
  | arg {Γ : Ctx} {q S D I : Tm} {l : Lvl} : InReg ⟨[Γ ⊢ .darg q S D ∶ .desc l I, .inert Γ S, .inertD (S :: Γ) l I.shift (.app D.shift (.var 0))],
      .inertD Γ l I (.darg q S D)⟩

end WizMeta.Spec
