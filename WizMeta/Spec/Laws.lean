import WizMeta.Spec.Fragments

/-!
# The first laws: statements, and the substitution calculus

Weakening and substitution are the first lemmas of every later proof (and substitution is
the law both of the kernel's 2026-11-10 `False` proofs broke). They are **stated** here for
any system, as properties `Weakening R`, `Substitution R`; they are **not proved** for
T0. With rules as data the proof is one closure property per rule set
(`Rules.RenStable` below is the shape for renaming), file by file.

Proved here: the laws of renaming and substitution on terms that those proofs start
from (identity and composition of renamings, and that substitution by variables is the
identity).
-/

namespace WizMeta
namespace Tm

theorem upRen_id : upRen id = id := by
  funext i; cases i <;> rfl

theorem upRen_comp (ρ ρ' : Nat → Nat) : upRen (ρ' ∘ ρ) = upRen ρ' ∘ upRen ρ := by
  funext i; cases i <;> rfl

theorem ren_id (t : Tm) : t.ren id = t := by
  induction t <;> simp_all [ren, upRen_id]

theorem ren_ren (t : Tm) : ∀ (ρ ρ' : Nat → Nat), (t.ren ρ).ren ρ' = t.ren (ρ' ∘ ρ) := by
  induction t <;> intro ρ ρ' <;> simp_all [ren, upRen_comp]

theorem upSub_var : upSub Tm.var = Tm.var := by
  funext i; cases i <;> rfl

theorem sub_var (t : Tm) : t.sub Tm.var = t := by
  induction t <;> simp_all [sub, upSub_var]

/-- Weakening twice is weakening by two. -/
theorem shift_shift (t : Tm) : t.shift.shift = t.shiftN 2 := by
  simp only [shift, shiftN, ren_ren]
  rfl

end Tm

namespace Spec

/-- The action of a renaming on a judgment whose context becomes `Δ`. -/
def Jdg.ren (ρ : Nat → Nat) (Δ : Ctx) : Jdg → Jdg
  | .wf _ => .wf Δ
  | .ty _ t A => .ty Δ (t.ren ρ) (A.ren ρ)
  | .eq _ t u A => .eq Δ (t.ren ρ) (u.ren ρ) (A.ren ρ)
  | .red _ t u A => .red Δ (t.ren ρ) (u.ren ρ) (A.ren ρ)
  | .inert _ A => .inert Δ (A.ren ρ)
  | .inertD _ l I D => .inertD Δ l (I.ren ρ) (D.ren ρ)
  | .peq _ l I X i D x y r => .peq Δ l (I.ren ρ) (X.ren ρ) (i.ren ρ) (D.ren ρ) (x.ren ρ) (y.ren ρ) (r.ren ρ)

/-- Weakening by one variable. -/
def Weakening (R : Rules) : Prop :=
  ∀ Γ t A B l, Derivable R (Γ ⊢ t ∶ A) → Derivable R (Γ ⊢ B ∶ .sort l) →
    Derivable R ((B :: Γ) ⊢ t.shift ∶ A.shift)

/-- Typing is stable under substitution (the plan's Subst, law L1 of the harness). -/
def Substitution (R : Rules) : Prop :=
  ∀ Γ A t B a, Derivable R ((A :: Γ) ⊢ t ∶ B) → Derivable R (Γ ⊢ a ∶ A) →
    Derivable R (Γ ⊢ t.inst a ∶ B.inst a)

/-- … and so is conversion. -/
def SubstitutionEq (R : Rules) : Prop :=
  ∀ Γ A t u B a, Derivable R ((A :: Γ) ⊢ t ≡ u ∶ B) → Derivable R (Γ ⊢ a ∶ A) →
    Derivable R (Γ ⊢ t.inst a ≡ u.inst a ∶ B.inst a)

/-- The type of a well-typed term is a type. -/
def Validity (R : Rules) : Prop :=
  ∀ Γ t A, Derivable R (Γ ⊢ t ∶ A) → ∃ l, Derivable R (Γ ⊢ A ∶ .sort l)

/-- Reduction preserves typing. -/
def SubjectReduction (R : Rules) : Prop :=
  ∀ Γ t u A, Derivable R (Γ ⊢ t ⟶ u ∶ A) → Derivable R (Γ ⊢ t ∶ A) ∧ Derivable R (Γ ⊢ u ∶ A)

end Spec
end WizMeta
