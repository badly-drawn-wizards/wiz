import WizMeta.Spec.Weakening

/-!
# Substitution for T0

The same shape as `Weakening.lean`: a substitution between contexts whose terms have the
renamed types (`SubOK`), a closure property per rule set (`SubClosed`), and the lemma for
T0. Lifting a substitution under a binder needs the renaming lemma (`T0_rename`).
-/

namespace WizMeta
namespace Tm

theorem sub_congr (t : Tm) {σ τ : Nat → Tm} (h : ∀ i, σ i = τ i) : t.sub σ = t.sub τ := by
  have : σ = τ := funext h
  rw [this]

theorem sub_inst (b a : Tm) (σ : Nat → Tm) : (b.inst a).sub σ = (b.sub (upSub σ)).inst (a.sub σ) := by
  simp only [inst, sub_sub]
  apply sub_congr; intro i; cases i with
  | zero => rfl
  | succ n => simp only [one, sub, upSub, shift, sub_ren]; exact (sub_var _).symm.trans (sub_congr _ fun _ => rfl)

theorem sub_shift (t : Tm) (σ : Nat → Tm) : t.shift.sub (upSub σ) = (t.sub σ).shift := by
  simp only [shift, sub_ren, ren_sub]; rfl

theorem sub_shift2 (t : Tm) (σ : Nat → Tm) : (t.shiftN 2).sub (upSub (upSub σ)) = (t.sub σ).shiftN 2 := by
  simp only [shiftN, sub_ren, ren_sub]
  apply sub_congr; intro i
  simp only [Function.comp, upSub, shift, ren_ren]; rfl

theorem sub_under1 (B : Tm) (σ : Nat → Tm) : (B.under 1).sub (upSub (upSub σ)) = (B.sub (upSub σ)).under 1 := by
  simp only [under, sub_ren, ren_sub]
  apply sub_congr; intro i; rcases i with _ | i
  · rfl
  · simp only [Function.comp, upRen, upSub, shift, ren_ren]; rfl

theorem sub_under2 (B : Tm) (σ : Nat → Tm) :
    (B.under 2).sub (upSub (upSub (upSub σ))) = (B.sub (upSub σ)).under 2 := by
  simp only [under, sub_ren, ren_sub]
  apply sub_congr; intro i; rcases i with _ | i
  · rfl
  · simp only [Function.comp, upRen, upSub, shift, ren_ren]; rfl

theorem sub_iff (a b : Tm) (σ : Nat → Tm) : (iff a b).sub σ = iff (a.sub σ) (b.sub σ) := by
  simp only [iff, sub, sub_shift, sub_shift2]

theorem sub_eqPi (A B f g : Tm) (σ : Nat → Tm) :
    (eqPi A B f g).sub σ = eqPi (A.sub σ) (B.sub (upSub σ)) (f.sub σ) (g.sub σ) := by
  simp only [eqPi, sub, sub_shift]; rfl

theorem sub_castPi (A₁ B₁ A₂ B₂ e t : Tm) (σ : Nat → Tm) :
    (castPi A₁ B₁ A₂ B₂ e t).sub σ =
      castPi (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) (e.sub σ) (t.sub σ) := by
  simp only [castPi, sub, sub_inst, sub_under1, sub_shift]; rfl

theorem sub_eqSigmaTransport (A B a b : Tm) (σ : Nat → Tm) :
    (eqSigmaTransport A B a b).sub (upSub σ) =
      eqSigmaTransport (A.sub σ) (B.sub (upSub σ)) (a.sub σ) (b.sub σ) := by
  simp only [eqSigmaTransport, sub, sub_shift, sub_shift2, sub_inst, sub_under2]; rfl

theorem sub_eqSigma (A B a b : Tm) (σ : Nat → Tm) :
    (eqSigma A B a b).sub σ = eqSigma (A.sub σ) (B.sub (upSub σ)) (a.sub σ) (b.sub σ) := by
  simp only [eqSigma, sub, sub_shift, sub_inst, sub_eqSigmaTransport]

theorem sub_eqSigmaProof (A B a b : Tm) (σ : Nat → Tm) :
    (eqSigmaProof A B a b).sub σ = eqSigmaProof (A.sub σ) (B.sub (upSub σ)) (a.sub σ) (b.sub σ) := by
  simp only [eqSigmaProof, sub, sub_shift, sub_inst]

theorem sub_eqTyPi (A₁ B₁ A₂ B₂ : Tm) (σ : Nat → Tm) :
    (eqTyPi A₁ B₁ A₂ B₂).sub σ = eqTyPi (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) := by
  simp only [eqTyPi, sub, sub_shift, sub_shift2, sub_inst, sub_under1, sub_under2]; rfl

theorem sub_eqTySigma (A₁ B₁ A₂ B₂ : Tm) (σ : Nat → Tm) :
    (eqTySigma A₁ B₁ A₂ B₂).sub σ = eqTySigma (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) := by
  simp only [eqTySigma, sub, sub_shift, sub_shift2, sub_inst, sub_under1, sub_under2]; rfl

theorem sub_castSigma (A₁ B₁ A₂ B₂ e t : Tm) (σ : Nat → Tm) :
    (castSigma A₁ B₁ A₂ B₂ e t).sub σ =
      castSigma (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) (e.sub σ) (t.sub σ) := by
  simp only [castSigma, sub, sub_inst]

theorem sub_transpMotiveTy (l : Lvl) (A a : Tm) (σ : Nat → Tm) :
    (transpMotiveTy l A a).sub σ = transpMotiveTy l (A.sub σ) (a.sub σ) := by
  simp only [transpMotiveTy, sub, sub_shift]; rfl

theorem sub_branches (bl : List Tm) (σ : Nat → Tm) : (branches bl).sub σ = branches (bl.map (sub σ)) := by
  induction bl with
  | nil => rfl
  | cons b bl ih => simp only [branches, sub, ih, List.map_cons]

theorem former_sub (t : Tm) (σ : Nat → Tm) {f : Former} (h : t.former? = some f) : (t.sub σ).former? = some f := by
  cases t <;> simp_all [former?, sub]

end Tm

namespace Spec

def Jdg.sub (σ : Nat → Tm) (Δ : Ctx) : Jdg → Jdg
  | .wf _ => .wf Δ
  | .ty _ t A => .ty Δ (t.sub σ) (A.sub σ)
  | .eq _ t u A => .eq Δ (t.sub σ) (u.sub σ) (A.sub σ)
  | .red _ t u A => .red Δ (t.sub σ) (u.sub σ) (A.sub σ)
  | .inert _ A => .inert Δ (A.sub σ)
  | .inertD _ l I D => .inertD Δ l (I.sub σ) (D.sub σ)
  | .peq _ l I X i D x y r => .peq Δ l (I.sub σ) (X.sub σ) (i.sub σ) (D.sub σ) (x.sub σ) (y.sub σ) (r.sub σ)

/-- `σ` sends each variable of `Γ` to a term of `Δ` of the substituted type. -/
def SubOK (R : Rules) (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ.lookup i = some A → Derivable R (Δ ⊢ σ i ∶ A.sub σ)

def Substs (R : Rules) (j : Jdg) : Prop :=
  ∀ σ Δ, SubOK R σ (Jdg.ctx j) Δ → Derivable R (.wf Δ) → Derivable R (Jdg.sub σ Δ j)

def SubClosed (S R : Rules) : Prop :=
  ∀ r, S r → (∀ p, p ∈ r.prems → Substs R p) → Substs R r.concl

theorem subst_of_closed {R : Rules} (h : SubClosed R R) {j : Jdg} (d : Derivable R j) : Substs R j := by
  induction d with
  | intro r hr _ ih => exact h r hr ih

theorem SubClosed.union {S S' R : Rules} (h : SubClosed S R) (h' : SubClosed S' R) : SubClosed (S ∪ S') R :=
  fun r hr ih => hr.elim (fun hs => h r hs ih) (fun hs => h' r hs ih)

theorem wfExt {R : Rules} (hc : ∀ r, Core r → R r) {Δ : Ctx} {A : Tm} {l : Lvl}
    (hΔ : Derivable R (.wf Δ)) (hA : Derivable R (Δ ⊢ A ∶ .sort l)) : Derivable R (.wf (A :: Δ)) :=
  ofRule (hc _ (.wfCons (l := l))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΔ, hA⟩)

/-- Lifting a substitution under a binder: the variables of `Γ` are weakened, which is
the renaming lemma. -/
theorem SubOK.up {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    {σ : Nat → Tm} {Γ Δ : Ctx} {A : Tm} {l : Lvl} (h : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ))
    (hA : Derivable R (Δ ⊢ A.sub σ ∶ .sort l)) : SubOK R (Tm.upSub σ) (A :: Γ) (A.sub σ :: Δ) := by
  intro i B hB
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hB; cases hB
    rw [Tm.sub_shift]
    exact ofRule (hc _ (.var (Ctx.lookup_zero _ _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact wfExt hc hΔ hA)
  | succ i =>
    rw [Ctx.lookup_succ] at hB
    cases hΓ : Ctx.lookup Γ i with
    | none => rw [hΓ] at hB; cases hB
    | some C =>
      rw [hΓ] at hB; cases hB
      rw [Tm.sub_shift]
      exact hren _ (h i C hΓ) Nat.succ _ (RenOK.succ Δ _) (wfExt hc hΔ hA)

theorem Substs.under {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    {Γ Δ : Ctx} {A : Tm} {l : Lvl} {σ : Nat → Tm}
    {j : Jdg} (hj : Substs R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Substs R (Γ ⊢ A ∶ .sort l)) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.sub (Tm.upSub σ) (A.sub σ :: Δ) j) :=
  have hA' := hA σ Δ hσ hΔ
  hj _ _ (hctx ▸ hσ.up hren hc hΔ hA') (wfExt hc hΔ hA')

theorem Substs.underD {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    {Γ Δ : Ctx} {A : Tm} {l : Lvl} {σ : Nat → Tm}
    {j : Jdg} (hj : Substs R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Derivable R (Δ ⊢ A.sub σ ∶ .sort l)) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.sub (Tm.upSub σ) (A.sub σ :: Δ) j) :=
  hj _ _ (hctx ▸ hσ.up hren hc hΔ hA) (wfExt hc hΔ hA)

theorem core_subClosed {R : Rules} (hc : ∀ r, Core r → R r) : SubClosed Core R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | wfNil => exact hΔ
  | wfCons => exact hΔ
  | var h => exact hσ _ _ h
  | sort => exact ofRule (hc _ .sort) (by fromIH ih σ Δ hσ hΔ)
  | sortCong h => exact ofRule (hc _ (.sortCong h)) (by fromIH ih σ Δ hσ hΔ)
  | conv => exact ofRule (hc _ .conv) (by fromIH ih σ Δ hσ hΔ)
  | eqConv => exact ofRule (hc _ .eqConv) (by fromIH ih σ Δ hσ hΔ)
  | redConv => exact ofRule (hc _ .redConv) (by fromIH ih σ Δ hσ hΔ)
  | refl => exact ofRule (hc _ .refl) (by fromIH ih σ Δ hσ hΔ)
  | symm => exact ofRule (hc _ .symm) (by fromIH ih σ Δ hσ hΔ)
  | trans => exact ofRule (hc _ .trans) (by fromIH ih σ Δ hσ hΔ)
  | redEq => exact ofRule (hc _ .redEq) (by fromIH ih σ Δ hσ hΔ)
  | irrel h => exact ofRule (hc _ (.irrel h)) (by fromIH ih σ Δ hσ hΔ)
  | eqProp h =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_iff]
    exact ofRule (hc _ (.eqProp h)) (by fromIH ih σ Δ hσ hΔ)
  | eqType h => exact ofRule (hc _ (.eqType h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTySort h => exact ofRule (hc _ (.eqTySort h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTySortApart h1 h2 h3 => exact ofRule (hc _ (.eqTySortApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | castSort h => exact ofRule (hc _ (.castSort h)) (by fromIH ih σ Δ hσ hΔ)


theorem pi_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r) (hp : ∀ r, Pi r → R r) : SubClosed Pi R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form h =>
    exact ofRule (hp _ (.form h)) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2 rfl ih.1 hσ hΔ)
  | lam =>
    exact ofRule (hp _ .lam) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2 rfl ih.2.1 hσ hΔ)
  | app =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .app) (by fromIH ih σ Δ hσ hΔ)
  | beta =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .beta) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2.1 rfl ih.2.1 hσ hΔ)
  | appRed =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .appRed) (by fromIH ih σ Δ hσ hΔ)
  | eta =>
    exact ofRule (hp _ .eta) (by
      fromIH ih σ Δ hσ hΔ
      have h := Substs.under hren hc ih.2.2.2 rfl ih.2.2.1 hσ hΔ
      simp only [Jdg.sub, Tm.sub, Tm.sub_shift] at h
      exact h)
  | cong h h' =>
    exact ofRule (hp _ (.cong h h')) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2 rfl ih.1 hσ hΔ)
  | appCong =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .appCong) (by fromIH ih σ Δ hσ hΔ)
  | eq h =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqPi]
    exact ofRule (hp _ (.eq h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hp _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_castPi]
    exact ofRule (hp _ (.cast h1 h2)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.1 rfl ih.2.2.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hσ hΔ)


theorem sigma_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r) (hs : ∀ r, Sigma r → R r) : SubClosed Sigma R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form h =>
    exact ofRule (hs _ (.form h)) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2 rfl ih.1 hσ hΔ)
  | pair =>
    exact ofRule (hs _ .pair) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | fst => exact ofRule (hs _ .fst) (by fromIH ih σ Δ hσ hΔ)
  | snd =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .snd) (by fromIH ih σ Δ hσ hΔ)
  | fstBeta =>
    exact ofRule (hs _ .fstBeta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | sndBeta =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .sndBeta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | fstRed => exact ofRule (hs _ .fstRed) (by fromIH ih σ Δ hσ hΔ)
  | sndRed =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .sndRed) (by fromIH ih σ Δ hσ hΔ)
  | eta =>
    exact ofRule (hs _ .eta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub, Tm.sub_inst] at h
      exact h)
  | cong h h' =>
    exact ofRule (hs _ (.cong h h')) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2 rfl ih.1 hσ hΔ)
  | fstCong => exact ofRule (hs _ .fstCong) (by fromIH ih σ Δ hσ hΔ)
  | sndCong =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .sndCong) (by fromIH ih σ Δ hσ hΔ)
  | eq h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqSigma]
    exact ofRule (hs _ (.eq h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqProof h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqSigmaProof]
    exact ofRule (hs _ (.eqProof h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hs _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_castSigma]
    exact ofRule (hs _ (.cast h1 h2)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.1 rfl ih.2.2.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hσ hΔ)


theorem unit_subClosed {R : Rules} (hu : ∀ r, Unit r → R r) : SubClosed Unit R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (hu _ .form) (by fromIH ih σ Δ hσ hΔ)
  | tt => exact ofRule (hu _ .tt) (by fromIH ih σ Δ hσ hΔ)
  | eta => exact ofRule (hu _ .eta) (by fromIH ih σ Δ hσ hΔ)
  | cong h => exact ofRule (hu _ (.cong h)) (by fromIH ih σ Δ hσ hΔ)
  | eq h => exact ofRule (hu _ (.eq h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih σ Δ hσ hΔ)


theorem empty_subClosed {R : Rules} (he : ∀ r, Empty r → R r) : SubClosed Empty R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (he _ .form) (by fromIH ih σ Δ hσ hΔ)
  | absurd => exact ofRule (he _ .absurd) (by fromIH ih σ Δ hσ hΔ)
  | cong h => exact ofRule (he _ (.cong h)) (by fromIH ih σ Δ hσ hΔ)
  | absurdCong => exact ofRule (he _ .absurdCong) (by fromIH ih σ Δ hσ hΔ)
  | eq h => exact ofRule (he _ (.eq h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (he _ (.eqTy h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (he _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 => exact ofRule (he _ (.cast h1 h2)) (by fromIH ih σ Δ hσ hΔ)


theorem let_subClosed {R : Rules} (hl : ∀ r, Let r → R r) : SubClosed Let R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | letE =>
    exact ofRule (hl _ .letE) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | zeta =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hl _ .zeta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | ann => exact ofRule (hl _ .ann) (by fromIH ih σ Δ hσ hΔ)
  | annRed => exact ofRule (hl _ .annRed) (by fromIH ih σ Δ hσ hΔ)


theorem eq_subClosed {R : Rules} (hq : ∀ r, Eq r → R r) : SubClosed Eq R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | eq => exact ofRule (hq _ .eq) (by fromIH ih σ Δ hσ hΔ)
  | refl => exact ofRule (hq _ .refl) (by fromIH ih σ Δ hσ hΔ)
  | reflTy => exact ofRule (hq _ .reflTy) (by fromIH ih σ Δ hσ hΔ)
  | transp =>
    exact ofRule (hq _ .transp) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2.2.1 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_transpMotiveTy] at h
      exact h)
  | cast => exact ofRule (hq _ .cast) (by fromIH ih σ Δ hσ hΔ)
  | eqCong => exact ofRule (hq _ .eqCong) (by fromIH ih σ Δ hσ hΔ)
  | eqTyCong => exact ofRule (hq _ .eqTyCong) (by fromIH ih σ Δ hσ hΔ)
  | castCong => exact ofRule (hq _ .castCong) (by fromIH ih σ Δ hσ hΔ)
  | eqRed => exact ofRule (hq _ .eqRed) (by fromIH ih σ Δ hσ hΔ)
  | eqTyRedL => exact ofRule (hq _ .eqTyRedL) (by fromIH ih σ Δ hσ hΔ)
  | eqTyRedR => exact ofRule (hq _ .eqTyRedR) (by fromIH ih σ Δ hσ hΔ)
  | castRedL => exact ofRule (hq _ .castRedL) (by fromIH ih σ Δ hσ hΔ)
  | castRedR => exact ofRule (hq _ .castRedR) (by fromIH ih σ Δ hσ hΔ)
  | eqAtProp h => exact ofRule (hq _ (.eqAtProp h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyProps h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_iff]
    exact ofRule (hq _ (.eqTyProps h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqTyFormers h1 h2 h3 h4 h5 =>
    exact ofRule (hq _ (.eqTyFormers h1 h2 (Tm.former_sub _ σ h3) (Tm.former_sub _ σ h4) h5))
      (by fromIH ih σ Δ hσ hΔ)


theorem eqTyCross_subClosed {R : Rules} (hx : ∀ r, EqTyCross r → R r) : SubClosed EqTyCross R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih σ Δ hσ hΔ)
  | propType h h' => exact ofRule (hx _ (.propType h h')) (by fromIH ih σ Δ hσ hΔ)
  | typeProp h h' => exact ofRule (hx _ (.typeProp h h')) (by fromIH ih σ Δ hσ hΔ)
  | pi h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTyPi]
    exact ofRule (hx _ (.pi h h')) (by fromIH ih σ Δ hσ hΔ)
  | sigma h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTySigma]
    exact ofRule (hx _ (.sigma h h')) (by fromIH ih σ Δ hσ hΔ)


theorem eqTyLevelled_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r) (hx : ∀ r, EqTyLevelled r → R r) :
    SubClosed EqTyLevelled R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih σ Δ hσ hΔ)
  | pi h1 h2 h3 h4 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTyPi]
    exact ofRule (hx _ (.pi h1 h2 h3 h4)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.1 rfl ih.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2 rfl ih.2.1 hσ hΔ)
  | sigma h1 h2 h3 h4 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTySigma]
    exact ofRule (hx _ (.sigma h1 h2 h3 h4)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.1 rfl ih.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2 rfl ih.2.1 hσ hΔ)


theorem branchPrems_sub {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl : List Tm} {σ : Nat → Tm}
    (h : ∀ p, p ∈ branchPrems Γ M n bl → Substs R p) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchPrems Δ (M.sub (Tm.upSub σ)) n (bl.map (Tm.sub σ)) → Derivable R p := by
  intro p hp
  simp only [branchPrems, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨b, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ∶ M.inst (.tag n k)) (by simp only [branchPrems, List.mem_map]; exact ⟨(b, k), hm, rfl⟩) σ Δ hσ hΔ
  simpa [Jdg.sub, Tm.sub_inst, Tm.sub] using this


theorem branchEqPrems_sub {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl bl' : List Tm} {σ : Nat → Tm}
    (h : ∀ p, p ∈ branchEqPrems Γ M n bl bl' → Substs R p) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchEqPrems Δ (M.sub (Tm.upSub σ)) n (bl.map (Tm.sub σ)) (bl'.map (Tm.sub σ)) → Derivable R p := by
  intro p hp
  simp only [branchEqPrems, List.zip_map, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨⟨b, b'⟩, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)) (by simp only [branchEqPrems, List.mem_map]; exact ⟨((b, b'), k), hm, rfl⟩) σ Δ hσ hΔ
  simpa [Jdg.sub, Tm.sub_inst, Tm.sub] using this


theorem enum_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r) (hn : ∀ r, Enum r → R r) : SubClosed Enum R := by
  intro r hr ih σ Δ hσ hΔ
  have hE : ∀ n, Derivable R (Δ ⊢ (Tm.enum n).sub σ ∶ .sort 1) := fun n =>
    ofRule (hn _ (.form (n := n))) (by fromIH ih σ Δ hσ hΔ)
  cases hr with
  | form => exact ofRule (hn _ .form) (by fromIH ih σ Δ hσ hΔ)
  | tag h => exact ofRule (hn _ (.tag h)) (by fromIH ih σ Δ hσ hΔ)
  | @ecase Γ s M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.ecase (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchPrems_sub ih2 hσ hΔ⟩)
  | @iota Γ b M k n i bl h1 h2 =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.iota (by simpa using h1) (by simp [h2]))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchPrems_sub ih2 hσ hΔ⟩)
  | @ecaseRed Γ s s' M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.ecaseRed (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchPrems_sub ih2 hσ hΔ⟩)
  | @ecaseCong Γ s s' M M' k n bl bl' h h' =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.ecaseCong (by simpa using h) (by simpa using h'))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchEqPrems_sub ih2 hσ hΔ⟩)
  | eqSame h => exact ofRule (hn _ (.eqSame h)) (by fromIH ih σ Δ hσ hΔ)
  | eqDiff h1 h2 h3 => exact ofRule (hn _ (.eqDiff h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqRedL => exact ofRule (hn _ .eqRedL) (by fromIH ih σ Δ hσ hΔ)
  | eqRedR => exact ofRule (hn _ .eqRedR) (by fromIH ih σ Δ hσ hΔ)
  | eqTySame => exact ofRule (hn _ .eqTySame) (by fromIH ih σ Δ hσ hΔ)
  | eqTyDiff h => exact ofRule (hn _ (.eqTyDiff h)) (by fromIH ih σ Δ hσ hΔ)
  | cast => exact ofRule (hn _ .cast) (by fromIH ih σ Δ hσ hΔ)


theorem global_subClosed {R : Rules} {sg : Sig} (hsg : Sig.Closed sg) (hg : ∀ r, Global sg r → R r) :
    SubClosed (Global sg) R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | @const Γ us c d h1 h2 =>
    have hd := (hsg _ (List.mem_of_find?_eq_some h1) us σ).1
    simp only [Jdg.sub, Tm.sub, hd]
    exact ofRule (hg _ (.const h1 h2)) (by fromIH ih σ Δ hσ hΔ)
  | @delta Γ v us c d h1 h2 h3 =>
    have hd := hsg _ (List.mem_of_find?_eq_some h1) us σ
    simp only [Jdg.sub, Tm.sub, hd.1, hd.2 _ h3]
    exact ofRule (hg _ (.delta h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | @cong Γ us us' c d h1 h2 h3 h4 =>
    have hd := (hsg _ (List.mem_of_find?_eq_some h1) us σ).1
    simp only [Jdg.sub, Tm.sub, hd]
    exact ofRule (hg _ (.cong h1 h2 h3 h4)) (by fromIH ih σ Δ hσ hΔ)

theorem T0_subClosedIn {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) {R : Rules}
    (hren : ∀ j, Derivable R j → Renames R j)
    (h : ∀ r, T0 sg var r → R r) (hc : ∀ r, Core r → R r) : SubClosed (T0 sg var) R := by
  refine ((((((((((core_subClosed hc).union (pi_subClosed hren hc fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr x))))))))))).union
    (sigma_subClosed hren hc fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr x)))))))))).union
    (unit_subClosed fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inl (.inr x))))))))).union
    (empty_subClosed fun _ x => h _ (.inl (.inl (.inl (.inl (.inl (.inr x)))))))).union
    (enum_subClosed hren hc fun _ x => h _ (.inl (.inl (.inl (.inl (.inr x))))))).union
    (let_subClosed fun _ x => h _ (.inl (.inl (.inl (.inr x)))))).union
    (global_subClosed hsg fun _ x => h _ (.inl (.inl (.inr x))))).union
    (eq_subClosed fun _ x => h _ (.inl (.inr x)))).union ?_)
  cases var with
  | cross => exact eqTyCross_subClosed fun _ x => h _ (.inr x)
  | levelled => exact eqTyLevelled_subClosed hren hc fun _ x => h _ (.inr x)

/-- **The substitution lemma for T0** (both variants). -/
theorem T0_subClosed {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) : SubClosed (T0 sg var) (T0 sg var) :=
  T0_subClosedIn hsg var (fun _ d => T0_rename hsg d) (fun _ x => x)
    fun _ h => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h))))))))

theorem T0_subst {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (T0 sg var) j) : Substs (T0 sg var) j :=
  subst_of_closed (T0_subClosed hsg var) d

/-- **Substitution for T0**, the plan's statement (`Spec.Substitution`) with the hypotheses it
needs: a closed signature and a well-formed context. -/
theorem T0_substitution {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {Γ : Ctx} {A t B a : Tm}
    (hΓ : Derivable (T0 sg var) (.wf Γ)) (ht : Derivable (T0 sg var) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (T0 sg var) (Γ ⊢ a ∶ A)) :
    Derivable (T0 sg var) (Γ ⊢ t.inst a ∶ B.inst a) := by
  refine T0_subst hsg ht (Tm.one a) Γ ?_ hΓ
  intro i C hC
  simp only [Jdg.ctx] at hC
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hC; cases hC
    simp only [Tm.shift, Tm.sub_ren]
    rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
    exact ha
  | succ i =>
    rw [Ctx.lookup_succ] at hC
    cases hΓi : Ctx.lookup Γ i with
    | none => rw [hΓi] at hC; cases hC
    | some D =>
      rw [hΓi] at hC; cases hC
      simp only [Tm.shift, Tm.sub_ren]
      rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
      exact ofRule (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (Core.var hΓi)))))))))) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]; exact hΓ)

theorem inReg_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r) (hi : ∀ r, InReg r → R r) : SubClosed InReg R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | castRefl => exact ofRule (hi _ .castRefl) (by fromIH ih σ Δ hσ hΔ)
  | conv => exact ofRule (hi _ .conv) (by fromIH ih σ Δ hσ hΔ)
  | enum => exact ofRule (hi _ .enum) (by fromIH ih σ Δ hσ hΔ)
  | unit h => exact ofRule (hi _ (.unit h)) (by fromIH ih σ Δ hσ hΔ)
  | ulift h => exact ofRule (hi _ (.ulift h)) (by fromIH ih σ Δ hσ hΔ)
  | sigma h =>
    exact ofRule (hi _ (.sigma h)) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2.2 rfl ih.2.1 hσ hΔ)
  | mu => exact ofRule (hi _ .mu) (by fromIH ih σ Δ hσ hΔ)
  | descConv => exact ofRule (hi _ .descConv) (by fromIH ih σ Δ hσ hΔ)
  | ret => exact ofRule (hi _ .ret) (by fromIH ih σ Δ hσ hΔ)
  | drec => exact ofRule (hi _ .drec) (by fromIH ih σ Δ hσ hΔ)
  | @argTag Γ q D I l k =>
    refine ofRule (hi _ .argTag) (List.forall_mem_cons.2 ⟨ih _ (List.mem_cons_self ..) σ Δ hσ hΔ, ?_⟩)
    intro p hp
    simp only [tagPrems, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ih (.inertD Γ l I (.app D (id (.tag k a)))) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩)) σ Δ hσ hΔ
  | @argTagLifted Γ q D I u l k =>
    refine ofRule (hi _ .argTagLifted) (List.forall_mem_cons.2 ⟨ih _ (List.mem_cons_self ..) σ Δ hσ hΔ, ?_⟩)
    intro p hp
    simp only [tagPrems, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ih (.inertD Γ l I (.app D (.up (.tag k a)))) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩)) σ Δ hσ hΔ
  | arg =>
    exact ofRule (hi _ .arg) (by
      fromIH ih σ Δ hσ hΔ
      have h := Substs.under hren hc ih.2.2.2 rfl ih.2.1 hσ hΔ
      simp only [Jdg.sub, Tm.sub, Tm.sub_shift] at h
      exact h)

/-- **The substitution lemma for T1.** -/
theorem T1_subst {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (T1 sg var) j) : Substs (T1 sg var) j := by
  have hren : ∀ j, Derivable (T1 sg var) j → Renames (T1 sg var) j := fun _ d => T1_rename hsg d
  have hc : ∀ r, Core r → T1 sg var r := fun _ h => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h)))))))))
  refine subst_of_closed ?_ d
  intro r hr ih
  rcases hr with hr | hr
  · exact (T0_subClosedIn hsg var hren (fun _ h => .inl h) hc) r hr ih
  · exact inReg_subClosed hren hc (fun _ h => .inr h) r hr ih

end Spec
end WizMeta
