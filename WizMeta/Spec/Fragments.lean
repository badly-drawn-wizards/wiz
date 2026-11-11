import WizMeta.Spec.Core
import WizMeta.Spec.Pi
import WizMeta.Spec.Sigma
import WizMeta.Spec.Unit
import WizMeta.Spec.Enum
import WizMeta.Spec.Let
import WizMeta.Spec.Global
import WizMeta.Spec.Eq
import WizMeta.Spec.EqTyCross
import WizMeta.Spec.EqTyLevelled
import WizMeta.Spec.InReg
import WizMeta.Spec.ULift
import WizMeta.Spec.Desc
import WizMeta.Spec.Mu
import WizMeta.Spec.DescEq
import WizMeta.Spec.PayloadKernel
import WizMeta.Spec.PayloadStuck
import WizMeta.Spec.PayloadUniform

/-!
# The fragments

    T0     Π, Σ, Unit, Empty, Enum, universes, let, globals, observational equality
    T1     T0 + regularity at inert types (InReg_conv)
    Tprog  T1 + ULift, Qty, descriptions, μ, equality and casts by codes (PR #40)
                                                     (levels are prenex in all three)

each in two variants, by the rule for an equation between two `Π`/`Σ` types
(`EqTyCross`: what the kernels implement; `EqTyLevelled`: CCobs's), and Tprog with one of
three rule sets for equations between constructors (`Payload*.lean`).

Missing from Tprog as the plan defines it: `ν` and its operations. Sizes and usage
checking are left out on purpose.
-/

namespace WizMeta.Spec

def eqTyRules : EqTyVariant → Rules
  | .cross => EqTyCross
  | .levelled => EqTyLevelled

def T0 (sg : Sig) (var : EqTyVariant := .cross) : Rules :=
  Core ∪ Pi ∪ Sigma ∪ Unit ∪ Empty ∪ Enum ∪ Let ∪ Global sg ∪ Eq ∪ eqTyRules var

def T1 (sg : Sig) (var : EqTyVariant := .cross) : Rules := T0 sg var ∪ InReg

/-- Tprog, with one of the three rule sets for equations between constructors
(`PayloadStuck`, `PayloadUniform`, or `PayloadKernel whnfTy`). -/
def Tprog (sg : Sig) (var : EqTyVariant := .cross) (payload : Rules := PayloadStuck) : Rules :=
  T1 sg var ∪ ULift var ∪ Desc ∪ Mu ∪ DescEq ∪ payload

theorem T0_sub_T1 {sg var j} (d : Derivable (T0 sg var) j) : Derivable (T1 sg var) j := d.union_left
theorem T1_sub_Tprog {sg var payload j} (d : Derivable (T1 sg var) j) : Derivable (Tprog sg var payload) j :=
  d.union_left.union_left.union_left.union_left.union_left

/-- A well-formed signature for a system `T`: each declaration has a fresh name, mentions
only its own level parameters, and is typed in the signature before it. -/
inductive SigWF (T : Sig → Rules) : Sig → Prop
  | nil : SigWF T []
  | axiom {sg : Sig} {d : Decl} {l : Lvl} : SigWF T sg → sg.find? d.name = none → d.value = none →
      d.type.lvlBound ≤ d.nparams → Derivable (T sg) ([] ⊢ d.type ∶ .sort l) → SigWF T (d :: sg)
  | defn {sg : Sig} {d : Decl} {l : Lvl} {v : Tm} : SigWF T sg → sg.find? d.name = none → d.value = some v →
      d.type.lvlBound ≤ d.nparams → v.lvlBound ≤ d.nparams →
      Derivable (T sg) ([] ⊢ d.type ∶ .sort l) → Derivable (T sg) ([] ⊢ v ∶ d.type) → SigWF T (d :: sg)

/-- Weak-head reduction of a relevant term: the relation WHN is about. No proof is
reduced: at a proposition this relation is empty. -/
def WhRed (T : Rules) (Γ : Ctx) (t u A : Tm) : Prop :=
  Derivable T (Γ ⊢ t ⟶ u ∶ A) ∧ ∃ l, Derivable T (Γ ⊢ A ∶ .sort l) ∧ ¬ l.IsZero

end WizMeta.Spec
