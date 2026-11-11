import WizMeta.Spec.Laws

/-!
# Weakening: the substitution calculus, and the renaming lemma rule set by rule set

The renaming lemma is stated for any renaming between contexts that respects the
variables' types (`RenOK`), not only for weakening at the head: a rule with a premise
under a binder needs the lemma at `upRen ρ`, so "weakening by one variable at the head"
(`Spec.Weakening`) is not an inductive statement.

The lemma is proved for a rule set `S` as a closure property `RenClosed S R`: every rule
of `S`, renamed, is derivable in `R` from the renamed premises. Then `Derivable R` is
closed under renaming when each of the sets `R` is made of is (`rename_of_closed`).
Done here: the calculus, every rule set of T0 and T1 (`T0_rename`, `T1_rename`,
`T0_weakening`). Not done: Tprog (ULift, Desc, μ, the payload rules), see `Laws.lean`.

What the proof needed from the rules (each a premise added on this branch): a rule with a
premise under a binder has the binder's type as a premise (`Pi.lam`, `Pi.beta`, `Pi.eta`,
`Pi.cong`, `Sigma.cong`, `InReg.sigma`, `InReg.arg`), since without an inversion lemma
`Γ ⊢ Π A B ∶ Sort s` does not give `Γ ⊢ A ∶ Sort i`; and the signature is closed.
-/

namespace WizMeta
namespace Tm

theorem upSub_upRen (σ : Nat → Tm) (ρ : Nat → Nat) : upSub σ ∘ upRen ρ = upSub (σ ∘ ρ) := by
  funext i; cases i <;> rfl

theorem sub_ren (t : Tm) : ∀ (σ : Nat → Tm) (ρ : Nat → Nat), (t.ren ρ).sub σ = t.sub (σ ∘ ρ) := by
  induction t <;> intro σ ρ <;> simp_all [ren, sub, upSub_upRen]

theorem ren_upSub (ρ : Nat → Nat) (σ : Nat → Tm) :
    (fun i => (upSub σ i).ren (upRen ρ)) = upSub (fun i => (σ i).ren ρ) := by
  funext i; cases i with
  | zero => rfl
  | succ n => simp only [upSub, shift, ren_ren]; rfl

theorem ren_sub (t : Tm) : ∀ (ρ : Nat → Nat) (σ : Nat → Tm), (t.sub σ).ren ρ = t.sub (fun i => (σ i).ren ρ) := by
  induction t <;> intro ρ σ <;> simp_all [ren, sub, ← ren_upSub]

theorem sub_upSub (σ τ : Nat → Tm) :
    (fun i => (upSub σ i).sub (upSub τ)) = upSub (fun i => (σ i).sub τ) := by
  funext i; cases i with
  | zero => rfl
  | succ n =>
    simp only [upSub, shift, sub_ren, ren_sub]
    rfl

theorem sub_sub (t : Tm) : ∀ (σ τ : Nat → Tm), (t.sub σ).sub τ = t.sub (fun i => (σ i).sub τ) := by
  induction t <;> intro σ τ <;> simp_all [sub, ← sub_upSub]

theorem ren_eq_sub (t : Tm) (ρ : Nat → Nat) : t.ren ρ = t.sub (fun i => .var (ρ i)) := by
  have h := sub_ren t Tm.var ρ
  rw [sub_var] at h
  exact h

/-- Renaming commutes with instantiating the innermost variable. -/
theorem ren_inst (b a : Tm) (ρ : Nat → Nat) : (b.inst a).ren ρ = (b.ren (upRen ρ)).inst (a.ren ρ) := by
  simp only [inst, ren_sub, sub_ren]
  congr 1; funext i; cases i <;> rfl

theorem ren_shift (t : Tm) (ρ : Nat → Nat) : t.shift.ren (upRen ρ) = (t.ren ρ).shift := by
  simp only [shift, ren_ren]; rfl

/-! ### The reducts commute with renaming -/

theorem ren_True' (ρ : Nat → Nat) : True'.ren ρ = True' := rfl
theorem ren_False' (ρ : Nat → Nat) : False'.ren ρ = False' := rfl

theorem upRen_succ (ρ : Nat → Nat) : upRen ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl

theorem ren_shift2 (t : Tm) (ρ : Nat → Nat) : (t.shiftN 2).ren (upRen (upRen ρ)) = (t.ren ρ).shiftN 2 := by
  simp only [shiftN, ren_ren]; rfl

theorem ren_iff (a b : Tm) (ρ : Nat → Nat) : (iff a b).ren ρ = iff (a.ren ρ) (b.ren ρ) := by
  simp only [iff, ren, ren_shift, ren_shift2]

theorem ren_eqPi (A B f g : Tm) (ρ : Nat → Nat) :
    (eqPi A B f g).ren ρ = eqPi (A.ren ρ) (B.ren (upRen ρ)) (f.ren ρ) (g.ren ρ) := by
  simp only [eqPi, ren, ren_shift]; rfl

theorem ren_under1 (B : Tm) (ρ : Nat → Nat) : (B.under 1).ren (upRen (upRen ρ)) = (B.ren (upRen ρ)).under 1 := by
  simp only [under, ren_ren]; congr 1; funext i; cases i <;> rfl

theorem ren_castPi (A₁ B₁ A₂ B₂ e t : Tm) (ρ : Nat → Nat) :
    (castPi A₁ B₁ A₂ B₂ e t).ren ρ =
      castPi (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) (e.ren ρ) (t.ren ρ) := by
  simp only [castPi, ren, ren_inst, ren_under1, ren_shift]; rfl

theorem ren_under2 (B : Tm) (ρ : Nat → Nat) :
    (B.under 2).ren (upRen (upRen (upRen ρ))) = (B.ren (upRen ρ)).under 2 := by
  simp only [under, ren_ren]; congr 1; funext i; rcases i with _ | _ | _ | i <;> rfl

theorem ren_eqSigmaTransport (A B a b : Tm) (ρ : Nat → Nat) :
    (eqSigmaTransport A B a b).ren (upRen ρ) =
      eqSigmaTransport (A.ren ρ) (B.ren (upRen ρ)) (a.ren ρ) (b.ren ρ) := by
  simp only [eqSigmaTransport, ren, ren_shift, ren_shift2, ren_inst, ren_under2]; rfl

theorem ren_eqSigma (A B a b : Tm) (ρ : Nat → Nat) :
    (eqSigma A B a b).ren ρ = eqSigma (A.ren ρ) (B.ren (upRen ρ)) (a.ren ρ) (b.ren ρ) := by
  simp only [eqSigma, ren, ren_shift, ren_inst, ren_eqSigmaTransport]

theorem ren_eqTyPi (A₁ B₁ A₂ B₂ : Tm) (ρ : Nat → Nat) :
    (eqTyPi A₁ B₁ A₂ B₂).ren ρ = eqTyPi (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) := by
  simp only [eqTyPi, ren, ren_shift, ren_shift2, ren_inst, ren_under1, ren_under2]; rfl

theorem ren_eqTySigma (A₁ B₁ A₂ B₂ : Tm) (ρ : Nat → Nat) :
    (eqTySigma A₁ B₁ A₂ B₂).ren ρ = eqTySigma (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) := by
  simp only [eqTySigma, ren, ren_shift, ren_shift2, ren_inst, ren_under1, ren_under2]; rfl

theorem ren_castSigma (A₁ B₁ A₂ B₂ e t : Tm) (ρ : Nat → Nat) :
    (castSigma A₁ B₁ A₂ B₂ e t).ren ρ =
      castSigma (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) (e.ren ρ) (t.ren ρ) := by
  simp only [castSigma, ren, ren_inst]

theorem ren_transpMotiveTy (l : Lvl) (A a : Tm) (ρ : Nat → Nat) :
    (transpMotiveTy l A a).ren ρ = transpMotiveTy l (A.ren ρ) (a.ren ρ) := by
  simp only [transpMotiveTy, ren, ren_shift]; rfl

theorem ren_branches (bl : List Tm) (ρ : Nat → Nat) : (branches bl).ren ρ = branches (bl.map (ren ρ)) := by
  induction bl with
  | nil => rfl
  | cons b bl ih => simp only [branches, ren, ih, List.map_cons]

theorem ren_instL (t : Tm) (us : List Lvl) (ρ : Nat → Nat) : (t.instL us).ren ρ = (t.ren ρ).instL us := by
  induction t generalizing ρ <;> simp_all [instL, ren]

theorem former_ren (t : Tm) (ρ : Nat → Nat) : (t.ren ρ).former? = t.former? := by
  cases t <;> rfl

end Tm

namespace Spec

/-- The context of a judgment. -/
def Jdg.ctx : Jdg → Ctx
  | .wf Γ | .ty Γ .. | .eq Γ .. | .red Γ .. | .inert Γ _ | .inertD Γ .. | .peq Γ .. => Γ

/-- `ρ` maps the variables of `Γ` to variables of `Δ` of the renamed types. -/
def RenOK (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ.lookup i = some A → Δ.lookup (ρ i) = some (A.ren ρ)

theorem Ctx.lookup_zero (A : Tm) (Γ : Ctx) : Ctx.lookup (A :: Γ) 0 = some A.shift := rfl

theorem Ctx.lookup_succ (A : Tm) (Γ : Ctx) (i : Nat) :
    Ctx.lookup (A :: Γ) (i + 1) = (Ctx.lookup Γ i).map Tm.shift := by
  simp only [Ctx.lookup, List.getElem?_cons_succ, Option.map_map]
  congr 1; funext t; simp only [Function.comp, Tm.shift, Tm.shiftN, Tm.ren_ren]; rfl

theorem RenOK.up {ρ : Nat → Nat} {Γ Δ : Ctx} (h : RenOK ρ Γ Δ) (A : Tm) :
    RenOK (Tm.upRen ρ) (A :: Γ) (A.ren ρ :: Δ) := by
  intro i B hB
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hB; cases hB
    rw [Tm.ren_shift]; rfl
  | succ i =>
    rw [Ctx.lookup_succ] at hB
    cases hΓ : Ctx.lookup Γ i with
    | none => rw [hΓ] at hB; cases hB
    | some C =>
      rw [hΓ] at hB; cases hB
      show Ctx.lookup (A.ren ρ :: Δ) (ρ i + 1) = _
      rw [Ctx.lookup_succ, h i C hΓ, Tm.ren_shift]; rfl

/-- The renaming lemma at one judgment, for a system `R`. -/
def Renames (R : Rules) (j : Jdg) : Prop :=
  ∀ ρ Δ, RenOK ρ (Jdg.ctx j) Δ → Derivable R (.wf Δ) → Derivable R (Jdg.ren ρ Δ j)

/-- Every rule of `S`, renamed, is derivable in `R` from its renamed premises. -/
def RenClosed (S R : Rules) : Prop :=
  ∀ r, S r → (∀ p, p ∈ r.prems → Renames R p) → Renames R r.concl

theorem rename_of_closed {R : Rules} (h : RenClosed R R) {j : Jdg} (d : Derivable R j) : Renames R j := by
  induction d with
  | intro r hr _ ih => exact h r hr ih

theorem RenClosed.union {S S' R : Rules} (h : RenClosed S R) (h' : RenClosed S' R) : RenClosed (S ∪ S') R :=
  fun r hr ih => hr.elim (fun hs => h r hs ih) (fun hs => h' r hs ih)

theorem ofRule {R : Rules} {ps : List Jdg} {c : Jdg} (h : R ⟨ps, c⟩) (hp : ∀ p, p ∈ ps → Derivable R p) :
    Derivable R c := .intro ⟨ps, c⟩ h hp

/-- Extending both contexts by a type of the source context. -/
theorem Renames.wfCons {R : Rules} (hc : ∀ r, Core r → R r) {Γ Δ : Ctx} {A : Tm} {l : Lvl} {ρ : Nat → Nat}
    (hA : Renames R (Γ ⊢ A ∶ .sort l)) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (.wf (A.ren ρ :: Δ)) :=
  ofRule (hc _ (.wfCons (l := l))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΔ, hA ρ Δ hρ hΔ⟩)

/-- Close the premise goal `∀ p ∈ ps, Derivable R p` from the renamed premises `I` (same
context) and the well-formed target context `hΔ`. -/
macro "fromIH " ih:ident ρ:ident Δ:ident hρ:ident hΔ:ident : tactic => `(tactic| (
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at $ih:ident ⊢
  repeat' apply And.intro
  all_goals try first | exact $hΔ | exact $ih $ρ $Δ $hρ $hΔ | exact $ih.1 $ρ $Δ $hρ $hΔ | exact $ih.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ))

theorem core_renClosed {R : Rules} (hc : ∀ r, Core r → R r) : RenClosed Core R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | wfNil => exact hΔ
  | wfCons => exact hΔ
  | var h => exact ofRule (hc _ (.var (hρ _ _ h))) (by fromIH ih ρ Δ hρ hΔ)
  | sort => exact ofRule (hc _ .sort) (by fromIH ih ρ Δ hρ hΔ)
  | sortCong h => exact ofRule (hc _ (.sortCong h)) (by fromIH ih ρ Δ hρ hΔ)
  | conv => exact ofRule (hc _ .conv) (by fromIH ih ρ Δ hρ hΔ)
  | eqConv => exact ofRule (hc _ .eqConv) (by fromIH ih ρ Δ hρ hΔ)
  | redConv => exact ofRule (hc _ .redConv) (by fromIH ih ρ Δ hρ hΔ)
  | refl => exact ofRule (hc _ .refl) (by fromIH ih ρ Δ hρ hΔ)
  | symm => exact ofRule (hc _ .symm) (by fromIH ih ρ Δ hρ hΔ)
  | trans => exact ofRule (hc _ .trans) (by fromIH ih ρ Δ hρ hΔ)
  | redEq => exact ofRule (hc _ .redEq) (by fromIH ih ρ Δ hρ hΔ)
  | irrel h => exact ofRule (hc _ (.irrel h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqProp h =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_iff]
    exact ofRule (hc _ (.eqProp h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqType h => exact ofRule (hc _ (.eqType h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTySort h => exact ofRule (hc _ (.eqTySort h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTySortApart h1 h2 h3 => exact ofRule (hc _ (.eqTySortApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | castSort h => exact ofRule (hc _ (.castSort h)) (by fromIH ih ρ Δ hρ hΔ)

/-- A premise under one binder, whose binder type is typed by another premise. -/
theorem Renames.under {R : Rules} (hc : ∀ r, Core r → R r) {Γ Δ : Ctx} {A : Tm} {l : Lvl} {ρ : Nat → Nat}
    {j : Jdg} (hj : Renames R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Renames R (Γ ⊢ A ∶ .sort l)) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.ren (Tm.upRen ρ) (A.ren ρ :: Δ) j) :=
  hj _ _ (hctx ▸ hρ.up A) (Renames.wfCons hc hA hρ hΔ)

theorem pi_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hp : ∀ r, Pi r → R r) : RenClosed Pi R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form h =>
    exact ofRule (hp _ (.form h)) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2 rfl ih.1 hρ hΔ)
  | lam =>
    exact ofRule (hp _ .lam) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2 rfl ih.2.1 hρ hΔ)
  | app =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .app) (by fromIH ih ρ Δ hρ hΔ)
  | beta =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .beta) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2.1 rfl ih.2.1 hρ hΔ)
  | appRed =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .appRed) (by fromIH ih ρ Δ hρ hΔ)
  | eta =>
    exact ofRule (hp _ .eta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := Renames.under hc ih.2.2.2 rfl ih.2.2.1 hρ hΔ
      simp only [Jdg.ren, Tm.ren, Tm.ren_shift] at h
      exact h)
  | cong h h' =>
    exact ofRule (hp _ (.cong h h')) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2 rfl ih.1 hρ hΔ)
  | appCong =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .appCong) (by fromIH ih ρ Δ hρ hΔ)
  | eq h =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqPi]
    exact ofRule (hp _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hp _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_castPi]
    exact ofRule (hp _ (.cast h1 h2)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.1 rfl ih.2.2.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hρ hΔ)

theorem sigma_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hs : ∀ r, Sigma r → R r) : RenClosed Sigma R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form h =>
    exact ofRule (hs _ (.form h)) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2 rfl ih.1 hρ hΔ)
  | pair =>
    exact ofRule (hs _ .pair) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | fst => exact ofRule (hs _ .fst) (by fromIH ih ρ Δ hρ hΔ)
  | snd =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .snd) (by fromIH ih ρ Δ hρ hΔ)
  | fstBeta =>
    exact ofRule (hs _ .fstBeta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | sndBeta =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .sndBeta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | fstRed => exact ofRule (hs _ .fstRed) (by fromIH ih ρ Δ hρ hΔ)
  | sndRed =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .sndRed) (by fromIH ih ρ Δ hρ hΔ)
  | eta =>
    exact ofRule (hs _ .eta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren, Tm.ren_inst] at h
      exact h)
  | cong h h' =>
    exact ofRule (hs _ (.cong h h')) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2 rfl ih.1 hρ hΔ)
  | fstCong => exact ofRule (hs _ .fstCong) (by fromIH ih ρ Δ hρ hΔ)
  | sndCong =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .sndCong) (by fromIH ih ρ Δ hρ hΔ)
  | eq h =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqSigma]
    exact ofRule (hs _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hs _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_castSigma]
    exact ofRule (hs _ (.cast h1 h2)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.1 rfl ih.2.2.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hρ hΔ)

theorem unit_renClosed {R : Rules} (hu : ∀ r, Unit r → R r) : RenClosed Unit R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (hu _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | tt => exact ofRule (hu _ .tt) (by fromIH ih ρ Δ hρ hΔ)
  | eta => exact ofRule (hu _ .eta) (by fromIH ih ρ Δ hρ hΔ)
  | cong h => exact ofRule (hu _ (.cong h)) (by fromIH ih ρ Δ hρ hΔ)
  | eq h => exact ofRule (hu _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih ρ Δ hρ hΔ)

theorem empty_renClosed {R : Rules} (he : ∀ r, Empty r → R r) : RenClosed Empty R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (he _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | absurd => exact ofRule (he _ .absurd) (by fromIH ih ρ Δ hρ hΔ)
  | cong h => exact ofRule (he _ (.cong h)) (by fromIH ih ρ Δ hρ hΔ)
  | absurdCong => exact ofRule (he _ .absurdCong) (by fromIH ih ρ Δ hρ hΔ)
  | eq h => exact ofRule (he _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (he _ (.eqTy h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (he _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 => exact ofRule (he _ (.cast h1 h2)) (by fromIH ih ρ Δ hρ hΔ)

theorem let_renClosed {R : Rules} (hl : ∀ r, Let r → R r) : RenClosed Let R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | letE =>
    exact ofRule (hl _ .letE) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | zeta =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hl _ .zeta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | ann => exact ofRule (hl _ .ann) (by fromIH ih ρ Δ hρ hΔ)
  | annRed => exact ofRule (hl _ .annRed) (by fromIH ih ρ Δ hρ hΔ)

theorem eq_renClosed {R : Rules} (hq : ∀ r, Eq r → R r) : RenClosed Eq R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | eq => exact ofRule (hq _ .eq) (by fromIH ih ρ Δ hρ hΔ)
  | refl => exact ofRule (hq _ .refl) (by fromIH ih ρ Δ hρ hΔ)
  | reflTy => exact ofRule (hq _ .reflTy) (by fromIH ih ρ Δ hρ hΔ)
  | transp =>
    exact ofRule (hq _ .transp) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2.2.1 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_transpMotiveTy] at h
      exact h)
  | cast => exact ofRule (hq _ .cast) (by fromIH ih ρ Δ hρ hΔ)
  | eqCong => exact ofRule (hq _ .eqCong) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyCong => exact ofRule (hq _ .eqTyCong) (by fromIH ih ρ Δ hρ hΔ)
  | castCong => exact ofRule (hq _ .castCong) (by fromIH ih ρ Δ hρ hΔ)
  | eqRed => exact ofRule (hq _ .eqRed) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyRedL => exact ofRule (hq _ .eqTyRedL) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyRedR => exact ofRule (hq _ .eqTyRedR) (by fromIH ih ρ Δ hρ hΔ)
  | castRedL => exact ofRule (hq _ .castRedL) (by fromIH ih ρ Δ hρ hΔ)
  | castRedR => exact ofRule (hq _ .castRedR) (by fromIH ih ρ Δ hρ hΔ)
  | eqAtProp h => exact ofRule (hq _ (.eqAtProp h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyProps h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_iff]
    exact ofRule (hq _ (.eqTyProps h h')) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyFormers h1 h2 h3 h4 h5 =>
    exact ofRule (hq _ (.eqTyFormers h1 h2 ((Tm.former_ren _ ρ).trans h3) ((Tm.former_ren _ ρ).trans h4) h5))
      (by fromIH ih ρ Δ hρ hΔ)

theorem eqTyCross_renClosed {R : Rules} (hx : ∀ r, EqTyCross r → R r) : RenClosed EqTyCross R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | propType h h' => exact ofRule (hx _ (.propType h h')) (by fromIH ih ρ Δ hρ hΔ)
  | typeProp h h' => exact ofRule (hx _ (.typeProp h h')) (by fromIH ih ρ Δ hρ hΔ)
  | pi h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTyPi]
    exact ofRule (hx _ (.pi h h')) (by fromIH ih ρ Δ hρ hΔ)
  | sigma h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTySigma]
    exact ofRule (hx _ (.sigma h h')) (by fromIH ih ρ Δ hρ hΔ)

theorem eqTyLevelled_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hx : ∀ r, EqTyLevelled r → R r) :
    RenClosed EqTyLevelled R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | pi h1 h2 h3 h4 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTyPi]
    exact ofRule (hx _ (.pi h1 h2 h3 h4)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.1 rfl ih.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2 rfl ih.2.1 hρ hΔ)
  | sigma h1 h2 h3 h4 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTySigma]
    exact ofRule (hx _ (.sigma h1 h2 h3 h4)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.1 rfl ih.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2 rfl ih.2.1 hρ hΔ)

/-- A premise under a binder whose renamed type is typed directly. -/
theorem Renames.underD {R : Rules} (hc : ∀ r, Core r → R r) {Γ Δ : Ctx} {A : Tm} {l : Lvl} {ρ : Nat → Nat}
    {j : Jdg} (hj : Renames R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Derivable R (Δ ⊢ A.ren ρ ∶ .sort l)) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.ren (Tm.upRen ρ) (A.ren ρ :: Δ) j) :=
  hj _ _ (hctx ▸ hρ.up A) (ofRule (hc _ (.wfCons (l := l))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΔ, hA⟩))

theorem branchPrems_ren {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl : List Tm} {ρ : Nat → Nat}
    (h : ∀ p, p ∈ branchPrems Γ M n bl → Renames R p) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchPrems Δ (M.ren (Tm.upRen ρ)) n (bl.map (Tm.ren ρ)) → Derivable R p := by
  intro p hp
  simp only [branchPrems, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨b, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ∶ M.inst (.tag n k)) (by simp only [branchPrems, List.mem_map]; exact ⟨(b, k), hm, rfl⟩) ρ Δ hρ hΔ
  simpa [Jdg.ren, Tm.ren_inst, Tm.ren] using this

theorem branchEqPrems_ren {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl bl' : List Tm} {ρ : Nat → Nat}
    (h : ∀ p, p ∈ branchEqPrems Γ M n bl bl' → Renames R p) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchEqPrems Δ (M.ren (Tm.upRen ρ)) n (bl.map (Tm.ren ρ)) (bl'.map (Tm.ren ρ)) → Derivable R p := by
  intro p hp
  simp only [branchEqPrems, List.zip_map, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨⟨b, b'⟩, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)) (by simp only [branchEqPrems, List.mem_map]; exact ⟨((b, b'), k), hm, rfl⟩) ρ Δ hρ hΔ
  simpa [Jdg.ren, Tm.ren_inst, Tm.ren] using this

theorem enum_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hn : ∀ r, Enum r → R r) : RenClosed Enum R := by
  intro r hr ih ρ Δ hρ hΔ
  have hE : ∀ n, Derivable R (Δ ⊢ (Tm.enum n).ren ρ ∶ .sort 1) := fun n =>
    ofRule (hn _ (.form (n := n))) (by fromIH ih ρ Δ hρ hΔ)
  cases hr with
  | form => exact ofRule (hn _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | tag h => exact ofRule (hn _ (.tag h)) (by fromIH ih ρ Δ hρ hΔ)
  | @ecase Γ s M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.ecase (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchPrems_ren ih2 hρ hΔ⟩)
  | @iota Γ b M k n i bl h1 h2 =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.iota (by simpa using h1) (by simp [h2]))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchPrems_ren ih2 hρ hΔ⟩)
  | @ecaseRed Γ s s' M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.ecaseRed (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchPrems_ren ih2 hρ hΔ⟩)
  | @ecaseCong Γ s s' M M' k n bl bl' h h' =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.ecaseCong (by simpa using h) (by simpa using h'))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchEqPrems_ren ih2 hρ hΔ⟩)
  | eqSame h => exact ofRule (hn _ (.eqSame h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqDiff h1 h2 h3 => exact ofRule (hn _ (.eqDiff h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqRedL => exact ofRule (hn _ .eqRedL) (by fromIH ih ρ Δ hρ hΔ)
  | eqRedR => exact ofRule (hn _ .eqRedR) (by fromIH ih ρ Δ hρ hΔ)
  | eqTySame => exact ofRule (hn _ .eqTySame) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyDiff h => exact ofRule (hn _ (.eqTyDiff h)) (by fromIH ih ρ Δ hρ hΔ)
  | cast => exact ofRule (hn _ .cast) (by fromIH ih ρ Δ hρ hΔ)

/-- Every declaration is closed, at every instance of its level parameters: substitution
leaves its type and value alone. (Implied by `SigWF` through "a term typed in the empty
context is closed", which is not proved; and needed: without it `Γ ⊢ c ∶ var 5` is
derivable for an ill-formed signature and its weakening is not. `Spec.Weakening` in
`Laws.lean` omits it.) -/
def Sig.Closed (sg : Sig) : Prop :=
  ∀ d, d ∈ sg → ∀ us σ, (d.type.instL us).sub σ = d.type.instL us ∧
    ∀ v, d.value = some v → (v.instL us).sub σ = v.instL us

theorem Sig.Closed.ren {sg : Sig} (h : Sig.Closed sg) {d : Decl} (hd : d ∈ sg) (us : List Lvl) (ρ : Nat → Nat) :
    (d.type.instL us).ren ρ = d.type.instL us ∧ ∀ v, d.value = some v → (v.instL us).ren ρ = v.instL us := by
  simp only [Tm.ren_eq_sub]
  exact ⟨(h d hd us _).1, (h d hd us _).2⟩

theorem global_renClosed {R : Rules} {sg : Sig} (hsg : Sig.Closed sg) (hg : ∀ r, Global sg r → R r) :
    RenClosed (Global sg) R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | @const Γ us c d h1 h2 =>
    have hd := (hsg.ren (List.mem_of_find?_eq_some h1) us ρ).1
    simp only [Jdg.ren, Tm.ren, hd]
    exact ofRule (hg _ (.const h1 h2)) (by fromIH ih ρ Δ hρ hΔ)
  | @delta Γ v us c d h1 h2 h3 =>
    have hd := hsg.ren (List.mem_of_find?_eq_some h1) us ρ
    simp only [Jdg.ren, Tm.ren, hd.1, hd.2 _ h3]
    exact ofRule (hg _ (.delta h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | @cong Γ us us' c d h1 h2 h3 h4 =>
    have hd := (hsg.ren (List.mem_of_find?_eq_some h1) us ρ).1
    simp only [Jdg.ren, Tm.ren, hd]
    exact ofRule (hg _ (.cong h1 h2 h3 h4)) (by fromIH ih ρ Δ hρ hΔ)

/-- **The renaming lemma for T0** (both variants): every judgment derivable in T0 stays
derivable under a renaming into a well-formed context that respects the variables' types. -/
theorem T0_renClosedIn {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) {R : Rules}
    (h : ∀ r, T0 sg var r → R r) (hc : ∀ r, Core r → R r) : RenClosed (T0 sg var) R := by
  refine ((((((((((core_renClosed hc).union (pi_renClosed hc fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr x))))))))))).union
    (sigma_renClosed hc fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr x)))))))))).union
    (unit_renClosed fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inl (.inr x))))))))).union
    (empty_renClosed fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inr x)))))))).union
    (enum_renClosed hc fun _ x => h _ (.inl (.inl (.inl (.inl (.inr x))))))).union
    (let_renClosed fun _ x => h _ (.inl (.inl (.inl (.inr x)))))).union
    (global_renClosed hsg fun _ x => h _ (.inl (.inl (.inr x))))).union
    (eq_renClosed fun _ x => h _ (.inl (.inr x)))).union ?_)
  cases var with
  | cross => exact eqTyCross_renClosed fun _ x => h _ (.inr x)
  | levelled => exact eqTyLevelled_renClosed hc fun _ x => h _ (.inr x)

/-- **The renaming lemma for T0** (both variants): every judgment derivable in T0 stays
derivable under a renaming into a well-formed context that respects the variables' types. -/
theorem T0_renClosed {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) : RenClosed (T0 sg var) (T0 sg var) :=
  T0_renClosedIn hsg var (fun _ x => x) fun _ x => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl x))))))))

theorem T0_rename {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (T0 sg var) j) : Renames (T0 sg var) j :=
  rename_of_closed (T0_renClosed hsg var) d

theorem RenOK.succ (Γ : Ctx) (B : Tm) : RenOK Nat.succ Γ (B :: Γ) := by
  intro i A h
  show Ctx.lookup (B :: Γ) (i + 1) = _
  rw [Ctx.lookup_succ, h]; rfl

/-- **Weakening for T0**, the plan's statement with the two hypotheses it needs: a closed
signature, and a well-formed context (`Spec.Weakening` omits both; the second would follow
from context validity, `Γ ⊢ J → ⊢ Γ`, which is not proved). -/
theorem T0_weakening {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {Γ : Ctx} {t A B : Tm} {l : Lvl}
    (hΓ : Derivable (T0 sg var) (.wf Γ)) (ht : Derivable (T0 sg var) (Γ ⊢ t ∶ A))
    (hB : Derivable (T0 sg var) (Γ ⊢ B ∶ .sort l)) :
    Derivable (T0 sg var) ((B :: Γ) ⊢ t.shift ∶ A.shift) :=
  T0_rename hsg ht Nat.succ (B :: Γ) (RenOK.succ Γ B)
    (ofRule (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (Core.wfCons (l := l)))))))))))
      (by simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hΓ, hB⟩))


theorem inReg_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hi : ∀ r, InReg r → R r) : RenClosed InReg R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | castRefl => exact ofRule (hi _ .castRefl) (by fromIH ih ρ Δ hρ hΔ)
  | conv => exact ofRule (hi _ .conv) (by fromIH ih ρ Δ hρ hΔ)
  | enum => exact ofRule (hi _ .enum) (by fromIH ih ρ Δ hρ hΔ)
  | unit h => exact ofRule (hi _ (.unit h)) (by fromIH ih ρ Δ hρ hΔ)
  | ulift h => exact ofRule (hi _ (.ulift h)) (by fromIH ih ρ Δ hρ hΔ)
  | sigma h =>
    exact ofRule (hi _ (.sigma h)) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2.2 rfl ih.2.1 hρ hΔ)
  | mu => exact ofRule (hi _ .mu) (by fromIH ih ρ Δ hρ hΔ)
  | descConv => exact ofRule (hi _ .descConv) (by fromIH ih ρ Δ hρ hΔ)
  | ret => exact ofRule (hi _ .ret) (by fromIH ih ρ Δ hρ hΔ)
  | drec => exact ofRule (hi _ .drec) (by fromIH ih ρ Δ hρ hΔ)
  | @argTag Γ q D I l k =>
    refine ofRule (hi _ .argTag) (List.forall_mem_cons.2 ⟨ih _ (List.mem_cons_self ..) ρ Δ hρ hΔ, ?_⟩)
    intro p hp
    simp only [tagPrems, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ih (.inertD Γ l I (.app D (id (.tag k a)))) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩)) ρ Δ hρ hΔ
  | @argTagLifted Γ q D I u l k =>
    refine ofRule (hi _ .argTagLifted) (List.forall_mem_cons.2 ⟨ih _ (List.mem_cons_self ..) ρ Δ hρ hΔ, ?_⟩)
    intro p hp
    simp only [tagPrems, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ih (.inertD Γ l I (.app D (.up (.tag k a)))) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩)) ρ Δ hρ hΔ
  | arg =>
    exact ofRule (hi _ .arg) (by
      fromIH ih ρ Δ hρ hΔ
      have h := Renames.under hc ih.2.2.2 rfl ih.2.1 hρ hΔ
      simp only [Jdg.ren, Tm.ren, Tm.ren_shift] at h
      exact h)

/-- **The renaming lemma for T1.** -/
theorem T1_rename {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (T1 sg var) j) : Renames (T1 sg var) j := by
  have hc : ∀ r, Core r → T1 sg var r := fun _ h => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h)))))))))
  refine rename_of_closed ?_ d
  intro r hr ih
  rcases hr with hr | hr
  · -- a rule of T0, read in T1: the same proofs, with T1 as the target system
    exact (T0_renClosedIn hsg var (fun _ h => .inl h) hc) r hr ih
  · exact inReg_renClosed hc (fun _ h => .inr h) r hr ih

end Spec
end WizMeta
