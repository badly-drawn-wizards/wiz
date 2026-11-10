import WizMeta.Spec.Rule

/-!
# Descriptions

`Desc.{l} I : Sort (l+2)` for an index type `I` in **exactly** `Sort (l+1)`; `ret`, `arg`,
`rec`, `hrec` with fields in exactly `Sort (l+1)`; the eliminator `Desc.elim`; and the
generic operations `⟦D⟧ X i`, `All D X P i xs`, `hyps D X P f i xs` as formers with one rule
per constructor.

A field's quantity is a term of type `Qty`. `⟦D⟧` computes when it is a literal (it
becomes the label of the `Σ`); at a quantity that is not a literal it is stuck.

Not here: `Desc.{l} I ≡ Desc.{l} I'` and casts between descriptions (PR #40's rules "by
codes" are not on master), except the injectivity of the former.
-/

namespace WizMeta.Spec
set_option autoImplicit true

/-- The premises typing `Desc.elim.{v} P mret marg mrec mhrec` on `Desc.{l} I`. -/
def delimPrems (Γ : Ctx) (l v : Lvl) (I P mret marg mrec mhrec : Tm) : List Jdg :=
  let (ta, tb, tc, th) := Tm.delimMethodTys l v I P
  [Γ ⊢ P ∶ .delimMotiveTy l v I, Γ ⊢ mret ∶ ta, Γ ⊢ marg ∶ tb, Γ ⊢ mrec ∶ tc, Γ ⊢ mhrec ∶ th]

inductive Desc : Rules
  | form : Desc ⟨[Γ ⊢ I ∶ .sort l.succ], Γ ⊢ .desc l I ∶ .sort l.succ.succ⟩
  | ret : Desc ⟨[Γ ⊢ .desc l I ∶ .sort l.succ.succ, Γ ⊢ i ∶ I], Γ ⊢ .dret i ∶ .desc l I⟩
  | arg : Desc ⟨[Γ ⊢ q ∶ .qty, Γ ⊢ S ∶ .sort l.succ, Γ ⊢ D ∶ .argContTy l I S], Γ ⊢ .darg q S D ∶ .desc l I⟩
  | drec : Desc ⟨[Γ ⊢ q ∶ .qty, Γ ⊢ j ∶ I, Γ ⊢ D ∶ .desc l I], Γ ⊢ .drec q j D ∶ .desc l I⟩
  | hrec : Desc ⟨[Γ ⊢ q ∶ .qty, Γ ⊢ H ∶ .sort l.succ, Γ ⊢ j ∶ .hrecIndexTy l I H, Γ ⊢ D ∶ .desc l I],
      Γ ⊢ .dhrec q H j D ∶ .desc l I⟩
  | cong : l.Equiv l' → Desc ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ], Γ ⊢ .desc l I ≡ .desc l' I' ∶ .sort l.succ.succ⟩
  | retCong : Desc ⟨[Γ ⊢ .desc l I ∶ .sort l.succ.succ, Γ ⊢ i ≡ i' ∶ I], Γ ⊢ .dret i ≡ .dret i' ∶ .desc l I⟩
  | argCong : Desc ⟨[Γ ⊢ q ≡ q' ∶ .qty, Γ ⊢ S ≡ S' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .argContTy l I S],
      Γ ⊢ .darg q S D ≡ .darg q' S' D' ∶ .desc l I⟩
  | recCong : Desc ⟨[Γ ⊢ q ≡ q' ∶ .qty, Γ ⊢ j ≡ j' ∶ I, Γ ⊢ D ≡ D' ∶ .desc l I],
      Γ ⊢ .drec q j D ≡ .drec q' j' D' ∶ .desc l I⟩
  | hrecCong : Desc ⟨[Γ ⊢ q ≡ q' ∶ .qty, Γ ⊢ H ≡ H' ∶ .sort l.succ, Γ ⊢ j ≡ j' ∶ .hrecIndexTy l I H,
        Γ ⊢ D ≡ D' ∶ .desc l I],
      Γ ⊢ .dhrec q H j D ≡ .dhrec q' H' j' D' ∶ .desc l I⟩
  -- the eliminator
  | elim : Desc ⟨(Γ ⊢ D ∶ .desc l I) :: delimPrems Γ l v I P mret marg mrec mhrec,
      Γ ⊢ .delim v P mret marg mrec mhrec D ∶ .app P D⟩
  | elimRet : Desc ⟨(Γ ⊢ .dret i ∶ .desc l I) :: delimPrems Γ l v I P mret marg mrec mhrec,
      Γ ⊢ .delim v P mret marg mrec mhrec (.dret i) ⟶ .app mret i ∶ .app P (.dret i)⟩
  | elimArg : Desc ⟨(Γ ⊢ .darg q S D ∶ .desc l I) :: delimPrems Γ l v I P mret marg mrec mhrec,
      Γ ⊢ .delim v P mret marg mrec mhrec (.darg q S D) ⟶ .delimArg v P mret marg mrec mhrec q S D
        ∶ .app P (.darg q S D)⟩
  | elimRec : Desc ⟨(Γ ⊢ .drec q j D ∶ .desc l I) :: delimPrems Γ l v I P mret marg mrec mhrec,
      Γ ⊢ .delim v P mret marg mrec mhrec (.drec q j D) ⟶ .delimRec v P mret marg mrec mhrec q j D
        ∶ .app P (.drec q j D)⟩
  | elimHrec : Desc ⟨(Γ ⊢ .dhrec q H j D ∶ .desc l I) :: delimPrems Γ l v I P mret marg mrec mhrec,
      Γ ⊢ .delim v P mret marg mrec mhrec (.dhrec q H j D) ⟶ .delimHrec v P mret marg mrec mhrec q H j D
        ∶ .app P (.dhrec q H j D)⟩
  | elimRed : Desc ⟨(Γ ⊢ D ⟶ D' ∶ .desc l I) :: delimPrems Γ l v I P mret marg mrec mhrec,
      Γ ⊢ .delim v P mret marg mrec mhrec D ⟶ .delim v P mret marg mrec mhrec D' ∶ .app P D⟩
  | elimCong : v.Equiv v' →
      Desc ⟨[Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ P ≡ P' ∶ .delimMotiveTy l v I,
          Γ ⊢ a ≡ a' ∶ (Tm.delimMethodTys l v I P).1, Γ ⊢ b ≡ b' ∶ (Tm.delimMethodTys l v I P).2.1,
          Γ ⊢ c ≡ c' ∶ (Tm.delimMethodTys l v I P).2.2.1, Γ ⊢ h ≡ h' ∶ (Tm.delimMethodTys l v I P).2.2.2],
        Γ ⊢ .delim v P a b c h D ≡ .delim v' P' a' b' c' h' D' ∶ .app P D⟩
  -- ⟦D⟧ X i
  | interp : Desc ⟨[Γ ⊢ D ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ i ∶ I], Γ ⊢ .interp l I D X i ∶ .sort l.succ⟩
  | interpRet : Desc ⟨[Γ ⊢ .dret j ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ i ∶ I],
      Γ ⊢ .interp l I (.dret j) X i ⟶ .interpRet l I j i ∶ .sort l.succ⟩
  | interpArg : Desc ⟨[Γ ⊢ .darg (.qlit q) S D ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ i ∶ I],
      Γ ⊢ .interp l I (.darg (.qlit q) S D) X i ⟶ .interpArg l q I S D X i ∶ .sort l.succ⟩
  | interpRec : Desc ⟨[Γ ⊢ .drec (.qlit q) j D ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ i ∶ I],
      Γ ⊢ .interp l I (.drec (.qlit q) j D) X i ⟶ .interpRec l q I j D X i ∶ .sort l.succ⟩
  | interpHrec : Desc ⟨[Γ ⊢ .dhrec (.qlit q) H j D ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ i ∶ I],
      Γ ⊢ .interp l I (.dhrec (.qlit q) H j D) X i ⟶ .interpHrec l q I H j D X i ∶ .sort l.succ⟩
  | interpRed : Desc ⟨[Γ ⊢ D ⟶ D' ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ i ∶ I],
      Γ ⊢ .interp l I D X i ⟶ .interp l I D' X i ∶ .sort l.succ⟩
  | interpCong : l.Equiv l' →
      Desc ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ X ≡ X' ∶ .familyTy l I, Γ ⊢ i ≡ i' ∶ I],
        Γ ⊢ .interp l I D X i ≡ .interp l' I' D' X' i' ∶ .sort l.succ⟩
  -- All D X P i xs and hyps D X P f i xs
  | all : Desc ⟨[Γ ⊢ D ∶ .desc l I, Γ ⊢ X ∶ .familyTy l I, Γ ⊢ P ∶ .predTy l v I X, Γ ⊢ i ∶ I,
        Γ ⊢ xs ∶ .interp l I D X i],
      Γ ⊢ .dall l v I D X P i xs ∶ .sort (Tm.allSort l v)⟩
  | hyps : Desc ⟨[Γ ⊢ .dall l v I D X P i xs ∶ .sort (Tm.allSort l v), Γ ⊢ f ∶ .sectionTy l v I X P],
      Γ ⊢ .dhyps l v I D X P f i xs ∶ .dall l v I D X P i xs⟩
  | allRet : Desc ⟨[Γ ⊢ .dall l v I (.dret j) X P i xs ∶ .sort (Tm.allSort l v)],
      Γ ⊢ .dall l v I (.dret j) X P i xs ⟶ .unit (Tm.allSort l v) ∶ .sort (Tm.allSort l v)⟩
  | allArg : Desc ⟨[Γ ⊢ .dall l v I (.darg (.qlit q) S D) X P i xs ∶ .sort (Tm.allSort l v)],
      Γ ⊢ .dall l v I (.darg (.qlit q) S D) X P i xs ⟶ .allArg l v I D X P i xs ∶ .sort (Tm.allSort l v)⟩
  | allRec : Desc ⟨[Γ ⊢ .dall l v I (.drec (.qlit q) j D) X P i xs ∶ .sort (Tm.allSort l v)],
      Γ ⊢ .dall l v I (.drec (.qlit q) j D) X P i xs ⟶ .allRec l v I j D X P i xs ∶ .sort (Tm.allSort l v)⟩
  | allHrec : Desc ⟨[Γ ⊢ .dall l v I (.dhrec (.qlit q) H j D) X P i xs ∶ .sort (Tm.allSort l v)],
      Γ ⊢ .dall l v I (.dhrec (.qlit q) H j D) X P i xs ⟶ .allHrec l v I H j D X P i xs ∶ .sort (Tm.allSort l v)⟩
  | allRed : Desc ⟨[Γ ⊢ .dall l v I D X P i xs ∶ .sort (Tm.allSort l v), Γ ⊢ D ⟶ D' ∶ .desc l I],
      Γ ⊢ .dall l v I D X P i xs ⟶ .dall l v I D' X P i xs ∶ .sort (Tm.allSort l v)⟩
  | hypsRet : Desc ⟨[Γ ⊢ .dhyps l v I (.dret j) X P f i xs ∶ .dall l v I (.dret j) X P i xs],
      Γ ⊢ .dhyps l v I (.dret j) X P f i xs ⟶ .tt ∶ .dall l v I (.dret j) X P i xs⟩
  | hypsArg : Desc ⟨[Γ ⊢ .dhyps l v I (.darg (.qlit q) S D) X P f i xs ∶ .dall l v I (.darg (.qlit q) S D) X P i xs],
      Γ ⊢ .dhyps l v I (.darg (.qlit q) S D) X P f i xs ⟶ .hypsArg l v I D X P f i xs
        ∶ .dall l v I (.darg (.qlit q) S D) X P i xs⟩
  | hypsRec : Desc ⟨[Γ ⊢ .dhyps l v I (.drec (.qlit q) j D) X P f i xs ∶ .dall l v I (.drec (.qlit q) j D) X P i xs],
      Γ ⊢ .dhyps l v I (.drec (.qlit q) j D) X P f i xs ⟶ .hypsRec l v I j D X P f i xs
        ∶ .dall l v I (.drec (.qlit q) j D) X P i xs⟩
  | hypsHrec : Desc ⟨[Γ ⊢ .dhyps l v I (.dhrec (.qlit q) H j D) X P f i xs ∶ .dall l v I (.dhrec (.qlit q) H j D) X P i xs],
      Γ ⊢ .dhyps l v I (.dhrec (.qlit q) H j D) X P f i xs ⟶ .hypsHrec l v I j D X P f i xs
        ∶ .dall l v I (.dhrec (.qlit q) H j D) X P i xs⟩
  | hypsRed : Desc ⟨[Γ ⊢ .dhyps l v I D X P f i xs ∶ .dall l v I D X P i xs, Γ ⊢ D ⟶ D' ∶ .desc l I],
      Γ ⊢ .dhyps l v I D X P f i xs ⟶ .dhyps l v I D' X P f i xs ∶ .dall l v I D X P i xs⟩
  | allCong : l.Equiv l' → v.Equiv v' →
      Desc ⟨[Γ ⊢ I ≡ I' ∶ .sort l.succ, Γ ⊢ D ≡ D' ∶ .desc l I, Γ ⊢ X ≡ X' ∶ .familyTy l I,
          Γ ⊢ P ≡ P' ∶ .predTy l v I X, Γ ⊢ i ≡ i' ∶ I, Γ ⊢ xs ≡ xs' ∶ .interp l I D X i],
        Γ ⊢ .dall l v I D X P i xs ≡ .dall l' v' I' D' X' P' i' xs' ∶ .sort (Tm.allSort l v)⟩
  | hypsCong : Desc ⟨[Γ ⊢ .dall l v I D X P i xs ≡ .dall l' v' I' D' X' P' i' xs' ∶ .sort (Tm.allSort l v),
        Γ ⊢ f ≡ f' ∶ .sectionTy l v I X P],
      Γ ⊢ .dhyps l v I D X P f i xs ≡ .dhyps l' v' I' D' X' P' f' i' xs' ∶ .dall l v I D X P i xs⟩
  /-- the former is injective -/
  | eqTy : l.Equiv l' →
      Desc ⟨[Γ ⊢ .desc l I ∶ .sort l.succ.succ, Γ ⊢ .desc l' I' ∶ .sort l'.succ.succ],
        Γ ⊢ .eqTy (.desc l I) (.desc l' I') ⟶ .eqTy I I' ∶ .sort 0⟩

end WizMeta.Spec
