import WizMeta.Reducts

/-!
# Judgments, and rules as data

The declarative system is not one big inductive type. A **rule** is a list of premises and
a conclusion; each former's file defines the set of its rule instances (a non-recursive
inductive predicate on `Rule`, one constructor per rule, side conditions as hypotheses);
a **system** is a union of such sets; and `Derivable R j` is the one inductive
definition: `j` is the conclusion of a rule of `R` whose premises are derivable.

So T0, T1 and Tprog are obtained by choosing files (`Fragments.lean`), a derivation in a
smaller system is one in a bigger system (`Derivable.mono`), and a proof about all
systems (weakening, substitution) is a property of each rule set, proved file by file.

Judgments:

    ⊢ Γ                    the context is well formed
    Γ ⊢ t ∶ A              typing (types are terms: `Γ ⊢ A ∶ Sort l`)
    Γ ⊢ t ≡ u ∶ A          conversion
    Γ ⊢ t ⟶ u ∶ A          one step of weak-head reduction
    Γ ⊢ A inert            `A` is first-order data (the side condition of T1)
    Γ ⊢ D inert-desc       … and a description all of whose fields are
    Γ ⊢ x ≐ y @ D ⟶ r      the equation between two payloads of `⟦D⟧ X i` computes to `r`

Reduction is a judgment of its own so that the rule a checker implements by a
contraction is told apart from one it implements in conversion (η, irrelevance, T1).
Every reduction is a conversion (`Core.redEq`). **Proofs are never reduced**: the
theorem to aim for (WHN) is about `Γ ⊢ t ⟶ u ∶ A` with `A` not a proposition; at a
proposition conversion holds by irrelevance and needs no reduction.
-/

namespace WizMeta

inductive Jdg where
  | wf (Γ : Ctx)
  | ty (Γ : Ctx) (t A : Tm)
  | eq (Γ : Ctx) (t u A : Tm)
  | red (Γ : Ctx) (t u A : Tm)
  | inert (Γ : Ctx) (A : Tm)
  | inertD (Γ : Ctx) (l : Lvl) (I D : Tm)
  /-- `x = y` at `⟦D⟧ X i`, by the description, is `r` -/
  | peq (Γ : Ctx) (l : Lvl) (I X i D x y r : Tm)

structure Rule where
  prems : List Jdg
  concl : Jdg

/-- A set of rule instances. -/
abbrev Rules := Rule → Prop

instance : Union Rules := ⟨fun R S r => R r ∨ S r⟩

inductive Derivable (R : Rules) : Jdg → Prop where
  | intro (r : Rule) (h : R r) (hp : ∀ p, p ∈ r.prems → Derivable R p) : Derivable R r.concl

theorem Derivable.mono {R S : Rules} (h : ∀ r, R r → S r) {j : Jdg} (d : Derivable R j) :
    Derivable S j := by
  induction d with
  | intro r hr _ ih => exact .intro r (h r hr) ih

theorem Derivable.union_left {R S : Rules} {j : Jdg} (d : Derivable R j) : Derivable (R ∪ S) j :=
  d.mono fun _ h => Or.inl h

theorem Derivable.union_right {R S : Rules} {j : Jdg} (d : Derivable S j) : Derivable (R ∪ S) j :=
  d.mono fun _ h => Or.inr h

namespace Spec

scoped notation:40 Γ " ⊢ " t " ∶ " A => Jdg.ty Γ t A
scoped notation:40 Γ " ⊢ " t " ≡ " u " ∶ " A => Jdg.eq Γ t u A
scoped notation:40 Γ " ⊢ " t " ⟶ " u " ∶ " A => Jdg.red Γ t u A

end Spec
end WizMeta
