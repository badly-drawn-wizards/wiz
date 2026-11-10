import WizMeta.Spec.Rule

/-!
# Enumerations

`Enum n : Sort 1`, tags, and `ecase` with a motive over the scrutinee. No η. An
enumeration is its size: labels are metadata and absent from the spec.
-/

namespace WizMeta.Spec
set_option autoImplicit true

/-- Each branch at the motive instantiated with its tag. -/
def branchPrems (Γ : Ctx) (M : Tm) (n : Nat) (bl : List Tm) : List Jdg :=
  bl.zipIdx.map fun (b, k) => Γ ⊢ b ∶ M.inst (.tag n k)

def branchEqPrems (Γ : Ctx) (M : Tm) (n : Nat) (bl bl' : List Tm) : List Jdg :=
  (bl.zip bl').zipIdx.map fun ((b, b'), k) => Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)

inductive Enum : Rules
  | form : Enum ⟨[.wf Γ], Γ ⊢ .enum n ∶ .sort 1⟩
  | tag : i < n → Enum ⟨[.wf Γ], Γ ⊢ .tag n i ∶ .enum n⟩
  | ecase : bl.length = n →
      Enum ⟨[Γ ⊢ s ∶ .enum n, (.enum n :: Γ) ⊢ M ∶ .sort k] ++ branchPrems Γ M n bl,
        Γ ⊢ .ecase M s (.branches bl) ∶ M.inst s⟩
  | iota : bl.length = n → bl[i]? = some b →
      Enum ⟨[.wf Γ, (.enum n :: Γ) ⊢ M ∶ .sort k] ++ branchPrems Γ M n bl,
        Γ ⊢ .ecase M (.tag n i) (.branches bl) ⟶ b ∶ M.inst (.tag n i)⟩
  | ecaseRed : bl.length = n →
      Enum ⟨[Γ ⊢ s ⟶ s' ∶ .enum n, (.enum n :: Γ) ⊢ M ∶ .sort k] ++ branchPrems Γ M n bl,
        Γ ⊢ .ecase M s (.branches bl) ⟶ .ecase M s' (.branches bl) ∶ M.inst s⟩
  | ecaseCong : bl.length = n → bl'.length = n →
      Enum ⟨[Γ ⊢ s ≡ s' ∶ .enum n, (.enum n :: Γ) ⊢ M ≡ M' ∶ .sort k] ++ branchEqPrems Γ M n bl bl',
        Γ ⊢ .ecase M s (.branches bl) ≡ .ecase M' s' (.branches bl') ∶ M.inst s⟩
  /-- an equation between two tags is decided; between anything else it is stuck -/
  | eqSame : i < n → Enum ⟨[.wf Γ], Γ ⊢ .eq (.enum n) (.tag n i) (.tag n i) ⟶ .True' ∶ .sort 0⟩
  | eqDiff : i < n → j < n → i ≠ j →
      Enum ⟨[.wf Γ], Γ ⊢ .eq (.enum n) (.tag n i) (.tag n j) ⟶ .False' ∶ .sort 0⟩
  | eqRedL : Enum ⟨[Γ ⊢ a ⟶ a' ∶ .enum n, Γ ⊢ b ∶ .enum n], Γ ⊢ .eq (.enum n) a b ⟶ .eq (.enum n) a' b ∶ .sort 0⟩
  | eqRedR : Enum ⟨[Γ ⊢ a ∶ .enum n, Γ ⊢ b ⟶ b' ∶ .enum n], Γ ⊢ .eq (.enum n) a b ⟶ .eq (.enum n) a b' ∶ .sort 0⟩
  | eqTySame : Enum ⟨[.wf Γ], Γ ⊢ .eqTy (.enum n) (.enum n) ⟶ .True' ∶ .sort 0⟩
  | eqTyDiff : n ≠ m → Enum ⟨[.wf Γ], Γ ⊢ .eqTy (.enum n) (.enum m) ⟶ .False' ∶ .sort 0⟩
  /-- the identity cast at an enumeration -/
  | cast : Enum ⟨[Γ ⊢ e ∶ .eqTy (.enum n) (.enum n), Γ ⊢ t ∶ .enum n], Γ ⊢ .cast (.enum n) (.enum n) e t ⟶ t ∶ .enum n⟩

end WizMeta.Spec
