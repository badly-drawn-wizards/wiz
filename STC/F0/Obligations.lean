import STC.F0.Renaming
/-!
# The M0 obligations, as `Prop`s

The design note (`/workspace/wiz-notes/stc-m0-spec.md` §5) asks F0 to **state** what its
metatheory will prove, not to prove it yet. This file is that list:

* `SoundF0 sg`: a checker exists that is sound, complete and total for F0 typing;
* `Con sg`: an axiom-free signature has no closed term of type `Empty prop`;
* `WHN sg`: a deterministic, typed weak-head strategy reaches a whnf at every relevant
  type (a proposition is excluded: `WhRed` is empty there);
* `DecConv sg`: conversion is decided by a sound and complete whnf-interleaved algorithm;
* `DecTC sg`: typing is decided by a sound and complete bidirectional algorithm.

The checker shape is `WizMeta/Checker.lean`'s: fuel-indexed, substitution-based, `M` a
result or a fuel/error. The functions themselves are M1 work; nothing here is proved.
-/


namespace STC
namespace F0
namespace Spec

inductive Err where
  /-- the fuel ran out: not a verdict -/
  | fuel
  /-- the term is rejected -/
  | fail (msg : String)
  deriving Repr, Inhabited

instance : ToString Err := ⟨fun | .fuel => "out of fuel" | .fail m => m⟩

abbrev M := Except Err

/-- A fuel-indexed checker: `some true` accepts, `some false` rejects, `none`/fuel is not
a verdict. This is the shape the M1 checker will have: no environments, no quotation. -/
abbrev Checker := Nat → Ctx → Tm → Tm → M Bool

/-- `check` never accepts an ill-typed term. -/
def Sound (check : Checker) (sg : Sig) : Prop :=
  ∀ n Γ t A, check n Γ t A = .ok true → Derivable (F0 sg) (Γ ⊢ t ∶ A)

/-- `check` accepts every well-typed term at some fuel. -/
def Complete (check : Checker) (sg : Sig) : Prop :=
  ∀ Γ t A, Derivable (F0 sg) (Γ ⊢ t ∶ A) → ∃ n, check n Γ t A = .ok true

/-- `check` rejects every ill-typed term at some fuel (it does not run out of fuel). -/
def Total (check : Checker) (sg : Sig) : Prop :=
  ∀ Γ t A, ¬ Derivable (F0 sg) (Γ ⊢ t ∶ A) → ∃ n, check n Γ t A = .ok false

/-- **`Sound(F0)`**: there is a sound, complete and total checker for F0. The proof is M1/M2
(the M1 checker plus the logical relation for completeness); M0 states it. -/
def SoundF0 (sg : Sig) : Prop :=
  ∃ check : Checker, Sound check sg ∧ Complete check sg ∧ Total check sg

/-- **`Con(F0)`**: for an axiom-free signature there is no closed proof of `Empty prop`.
The route is PT23's set model of codes plus the Σ/Unit/Enum/ULift cases of the model memo;
no mechanised model in M0. `castRefl` is not a rule, so consistency is relative to a
signature that does not declare it. -/
def Con (sg : Sig) : Prop :=
  AxiomFree sg → ∀ t : Tm, ¬ Derivable (F0 sg) (([] : Ctx) ⊢ t ∶ .empty .prop)

/-- A weak-head normal form: well typed, and no further reduction step. -/
def Whnf (sg : Sig) (Γ : Ctx) (t A : Tm) : Prop :=
  Derivable (F0 sg) (Γ ⊢ t ∶ A) ∧ ¬ ∃ u, Derivable (F0 sg) (Γ ⊢ t ⟶ u ∶ A)

/-- The reflexive-transitive closure of one-step reduction at a fixed type. -/
def RedStar (sg : Sig) (Γ : Ctx) (A t u : Tm) : Prop :=
  t = u ∨ Relation.TransGen (fun x y => Derivable (F0 sg) (Γ ⊢ x ⟶ y ∶ A)) t u

/-- A typed, fuel-indexed weak-head strategy: `whnf fuel Γ A t` tries to reduce `t` (a
term of type `A`) to a whnf. -/
abbrev WhnfStrategy := Nat → Ctx → Tm → Tm → Option Tm

/-- **`WHN`**: a deterministic weak-head strategy reaches a whnf at every term of a type
that is not a proposition. At a proposition no proof is reduced (`WhRed` is empty there),
so the hypothesis `s.NeverZero` is essential. The emptiness of `WhRed` at a proposition
needs the sorting lemma `SortUniqueAt` (`F0/WhRed.lean`); see the note there. -/
def WHN (sg : Sig) : Prop :=
  ∃ whnf : WhnfStrategy,
    (∀ n Γ A t u, whnf n Γ A t = some u → RedStar sg Γ A t u ∧ Whnf sg Γ u A) ∧
    (∀ Γ A t s, Derivable (F0 sg) (Γ ⊢ t ∶ A) → Derivable (F0 sg) (Γ ⊢ A ∶ .sort s) →
      s.NeverZero → ∃ n u, whnf n Γ A t = some u)

/-- A conversion checker: `conv fuel Γ t u A` decides `Γ ⊢ t ≡ u ∶ A`. -/
abbrev ConvChecker := Nat → Ctx → Tm → Tm → Tm → M Bool

/-- **`DecConv`**: conversion is decided by a typed, whnf-interleaved algorithm (proof
irrelevance at `Prop` first; η at Π/Σ/Unit/ULift; tags; neutral spines), sound and
complete. -/
def DecConv (sg : Sig) : Prop :=
  ∃ conv : ConvChecker,
    (∀ n Γ t u A, conv n Γ t u A = .ok true → Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A)) ∧
    (∀ n Γ t u A, conv n Γ t u A = .ok false → ¬ Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A)) ∧
    (∀ Γ t u A, Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A) → ∃ n, conv n Γ t u A = .ok true)

/-- A bidirectional typing checker: `tc fuel Γ t A` decides `Γ ⊢ t ⇐ A`. -/
abbrev TCChecker := Nat → Ctx → Tm → Tm → M Bool

/-- **`DecTC`**: bidirectional typing is sound and complete, hence decidable. -/
def DecTC (sg : Sig) : Prop :=
  ∃ tc : TCChecker,
    (∀ n Γ t A, tc n Γ t A = .ok true → Derivable (F0 sg) (Γ ⊢ t ∶ A)) ∧
    (∀ n Γ t A, tc n Γ t A = .ok false → ¬ Derivable (F0 sg) (Γ ⊢ t ∶ A)) ∧
    (∀ Γ t A, Derivable (F0 sg) (Γ ⊢ t ∶ A) → ∃ n, tc n Γ t A = .ok true)

end Spec
end F0
end STC
