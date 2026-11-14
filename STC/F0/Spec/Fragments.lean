import STC.F0.Spec.Core
import STC.F0.Spec.Pi
import STC.F0.Spec.Sigma
import STC.F0.Spec.Unit
import STC.F0.Spec.Enum
import STC.F0.Spec.Let
import STC.F0.Spec.Global
import STC.F0.Spec.Eq
import STC.F0.Spec.EqTyLevelled
import STC.F0.Spec.EqTyCross
import STC.F0.Spec.ULift
/-!
# F0: the fragment, and its signature and weak-head-reduction notions

    F0       Core, Π, Σ, Unit, Empty, Enum, let/letUnit/ann, closed globals,
             observational Eq, **levelled** Eq-Π/Eq-Σ, ULift
    F0Cross  the same with the cross-level Eq-Π/Eq-Σ (the kernels' rule); a variant for
             the divergence table, never used in the obligations

Regularity (`InReg`), descriptions, `μ`, `ν`, sizes and quantities are absent: not
"unproved" but unrepresentable in the term type.

The union is left-associative, as in `WizMeta`; the `*_in_F0Rules` lemmas name each
component's position once, so the renaming proof does not spell the `Or.inl` chains.
-/


namespace STC
namespace F0
namespace Spec

def eqTyRules : EqTyVariant → Rules
  | .cross => EqTyCross
  | .levelled => EqTyLevelled

/-- F0's rules and the cross-level variant, in the same shape. -/
def F0Rules (sg : Sig) (var : EqTyVariant) : Rules :=
  Core ∪ Pi ∪ Sigma ∪ Unit ∪ Empty ∪ Enum ∪ Let ∪ Global sg ∪ Eq ∪ eqTyRules var ∪ ULift var

/-- **F0**: the fragment of the design note, with levelled `Π`/`Σ` equality. -/
def F0 (sg : Sig) : Rules := F0Rules sg .levelled

/-- The cross-level variant (what the kernels implement), for the divergence table. -/
def F0Cross (sg : Sig) : Rules := F0Rules sg .cross

theorem core_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Core r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))))

theorem pi_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Pi r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))

theorem sigma_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Sigma r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))

theorem unit_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Unit r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))

theorem empty_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Empty r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))

theorem enum_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Enum r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))

theorem let_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Let r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem global_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Global sg r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem eq_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Eq r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inr h))

theorem eqTy_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : eqTyRules var r) :
    F0Rules sg var r :=
  Or.inl (Or.inr h)

theorem ulift_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : ULift var r) :
    F0Rules sg var r :=
  Or.inr h

/-! ## Signatures -/

/-- Every declaration is closed: substituting any terms leaves its type (and value) alone.
Needed by the renaming lemma; not implied by `SigWF` without "typed in the empty context
implies closed", which is not proved. -/
def Sig.Closed (sg : Sig) : Prop :=
  ∀ d, d ∈ sg → ∀ σ : Nat → Tm, d.type.sub σ = d.type ∧
    ∀ v, d.value = some v → v.sub σ = v

/-- A well-formed signature for a system `T`: each declaration has a fresh name and is
typed in the signature before it (closed; no level parameters in F0). -/
inductive SigWF (T : Sig → Rules) : Sig → Prop
  | nil : SigWF T []
  | axiom {sg : Sig} {d : Decl} {s : Srt} : SigWF T sg → sg.find? d.name = none → d.value = none →
      Derivable (T sg) (([] : Ctx) ⊢ d.type ∶ .sort s) → SigWF T (d :: sg)
  | defn {sg : Sig} {d : Decl} {s : Srt} {v : Tm} : SigWF T sg → sg.find? d.name = none →
      d.value = some v → Derivable (T sg) (([] : Ctx) ⊢ d.type ∶ .sort s) →
      Derivable (T sg) (([] : Ctx) ⊢ v ∶ d.type) → SigWF T (d :: sg)

/-- No declaration is an axiom: consistency is claimed for such signatures only. -/
def AxiomFree (sg : Sig) : Prop := ∀ d, d ∈ sg → d.value.isSome = true

/-- Weak-head reduction of a relevant term: the relation WHN is about. No proof is
reduced: at a proposition this relation is empty (the sort of `A` is never `prop`). -/
def WhRed (T : Rules) (Γ : Ctx) (t u A : Tm) : Prop :=
  Derivable T (Γ ⊢ t ⟶ u ∶ A) ∧ ∃ s, Derivable T (Γ ⊢ A ∶ .sort s) ∧ s.NeverZero

end Spec
end F0
end STC
