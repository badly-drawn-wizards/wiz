import WizMeta.Spec.Rule

/-!
# Equality and casts by codes (PR #40; CoreSpec §8.4b; model memo rows D1–D11, C10, C11)

**Equality at `Desc l I`, by the two heads** (memo D1–D7, E9):

    ret j        = ret j'          ⟶  j =_I j'
    arg q S E    = arg q S' E'     ⟶  (0 e : S ≡ S') × ((0 s : S) → E s =_{Desc I} E' (cast S S' e s))
    rec q j E    = rec q j' E'     ⟶  (0 _ : j =_I j') × (E =_{Desc I} E')
    hrec q H j E = hrec q H' j' E' ⟶  (0 _ : (0 e : H ≡ H') × ((0 h : H) → j h =_I j' (cast H H' e h))) × (E = E')
    two different literal quantities ⟶  False;  a quantity that is not known equal ⟶ stuck (no rule)
    two different constructors     ⟶  False
    a neutral on either side       ⟶  stuck (no rule)

The quantities of the two fields are compared by conversion at `Qty` (premise `q ≡ q'`),
and are `False` only as two different *literals*: a variable can become either.

**`μ ≡ μ` by codes** (memo D8): `μ_l I D i ≡ μ_l' I' D' i' ⟶ (I, D, i) =_T (I', D', i')`
at `T = (J : Sort (l+1)) × Desc_l J × J`, for `l ≡ l'`. The Σ rule (`Sigma.eq`) computes it
further (D9). No sizes here: `μ` is `μ^∞`, so the size condition of the kernels is vacuous.

**Casts** (memo C10, C11, D10, D11): between two descriptions constructor by constructor
(along `e : I ≡ I'`, which is what `Desc l I ≡ Desc l' I'` computes to by `Desc.eqTy`);
between two `μ` on a constructor, along the payload equation, one `transp` of `e` at `T`
(`Tm.muPayloadEq`). Its motive is in `Sort (imax (l+2) 1)`, so this needs the level-correct
`transpMotiveTy` (review D1). A cast at `Desc` or `μ` reduces its argument to find the
constructor (`castRedArg`).

Equations *between constructors* (`con x = con y`) are not here: they are the three
switchable `Payload*.lean` files, unchanged by PR #40.
-/

namespace WizMeta.Spec

inductive DescEq : Rules
  -- equality at `Desc l I`
  | eqRet {Γ : Ctx} {I j j' : Tm} {l : Lvl} : DescEq ⟨[Γ ⊢ .dret j ∶ .desc l I, Γ ⊢ .dret j' ∶ .desc l I],
      Γ ⊢ .eq (.desc l I) (.dret j) (.dret j') ⟶ .eq I j j' ∶ .sort 0⟩
  | eqArg {Γ : Ctx} {I q q' S S' E E' : Tm} {l : Lvl} : DescEq ⟨[Γ ⊢ .darg q S E ∶ .desc l I, Γ ⊢ .darg q' S' E' ∶ .desc l I, Γ ⊢ q ≡ q' ∶ .qty],
      Γ ⊢ .eq (.desc l I) (.darg q S E) (.darg q' S' E') ⟶ Tm.eqDescArg l I S S' E E' ∶ .sort 0⟩
  | eqRec {Γ : Ctx} {I q q' j j' E E' : Tm} {l : Lvl} : DescEq ⟨[Γ ⊢ .drec q j E ∶ .desc l I, Γ ⊢ .drec q' j' E' ∶ .desc l I, Γ ⊢ q ≡ q' ∶ .qty],
      Γ ⊢ .eq (.desc l I) (.drec q j E) (.drec q' j' E') ⟶ Tm.eqDescRec l I j j' E E' ∶ .sort 0⟩
  | eqHrec {Γ : Ctx} {I q q' H H' j j' E E' : Tm} {l : Lvl} :
      DescEq ⟨[Γ ⊢ .dhrec q H j E ∶ .desc l I, Γ ⊢ .dhrec q' H' j' E' ∶ .desc l I, Γ ⊢ q ≡ q' ∶ .qty],
        Γ ⊢ .eq (.desc l I) (.dhrec q H j E) (.dhrec q' H' j' E') ⟶ Tm.eqDescHrec l I H H' j j' E E' ∶ .sort 0⟩
  /-- the same constructor, with two different literal quantities -/
  | eqQtyApart {Γ : Ctx} {I D D' : Tm} {l : Lvl} {q q' : Q} {c : Nat} :
      D.dctor? = some c → D'.dctor? = some c → D.dqty? = some (.qlit q) → D'.dqty? = some (.qlit q') → q ≠ q' →
      DescEq ⟨[Γ ⊢ D ∶ .desc l I, Γ ⊢ D' ∶ .desc l I], Γ ⊢ .eq (.desc l I) D D' ⟶ .False' ∶ .sort 0⟩
  | eqCtors {Γ : Ctx} {I D D' : Tm} {l : Lvl} {c c' : Nat} : D.dctor? = some c → D'.dctor? = some c' → c ≠ c' →
      DescEq ⟨[Γ ⊢ D ∶ .desc l I, Γ ⊢ D' ∶ .desc l I], Γ ⊢ .eq (.desc l I) D D' ⟶ .False' ∶ .sort 0⟩
  -- the sides are reduced to find their heads
  | eqRedL {Γ : Ctx} {I D D₁ D' : Tm} {l : Lvl} : DescEq ⟨[Γ ⊢ D ⟶ D₁ ∶ .desc l I, Γ ⊢ D' ∶ .desc l I],
      Γ ⊢ .eq (.desc l I) D D' ⟶ .eq (.desc l I) D₁ D' ∶ .sort 0⟩
  | eqRedR {Γ : Ctx} {I D D' D₁ : Tm} {l : Lvl} : DescEq ⟨[Γ ⊢ D ∶ .desc l I, Γ ⊢ D' ⟶ D₁ ∶ .desc l I],
      Γ ⊢ .eq (.desc l I) D D' ⟶ .eq (.desc l I) D D₁ ∶ .sort 0⟩
  -- `μ ≡ μ` by codes
  | eqTyMu {Γ : Ctx} {I D i I' D' i' : Tm} {l l' : Lvl} : l.Equiv l' →
      DescEq ⟨[Γ ⊢ .mu l I D i ∶ .sort l.succ, Γ ⊢ .mu l' I' D' i' ∶ .sort l'.succ],
        Γ ⊢ .eqTy (.mu l I D i) (.mu l' I' D' i') ⟶ .eq (Tm.famCodeTy l) (Tm.code I D i) (Tm.code I' D' i') ∶ .sort 0⟩
  -- casts between descriptions, constructor by constructor
  | castRet {Γ : Ctx} {I I' e i : Tm} {l l' : Lvl} : l.Equiv l' →
      DescEq ⟨[Γ ⊢ .desc l' I' ∶ .sort l'.succ.succ, Γ ⊢ e ∶ .eqTy (.desc l I) (.desc l' I'), Γ ⊢ .dret i ∶ .desc l I],
        Γ ⊢ .cast (.desc l I) (.desc l' I') e (.dret i) ⟶ .dret (.cast I I' e i) ∶ .desc l' I'⟩
  | castArg {Γ : Ctx} {I I' e q S E : Tm} {l l' : Lvl} : l.Equiv l' →
      DescEq ⟨[Γ ⊢ .desc l' I' ∶ .sort l'.succ.succ, Γ ⊢ e ∶ .eqTy (.desc l I) (.desc l' I'), Γ ⊢ .darg q S E ∶ .desc l I],
        Γ ⊢ .cast (.desc l I) (.desc l' I') e (.darg q S E) ⟶ Tm.castDescArg l I I' e q S E ∶ .desc l' I'⟩
  | castRec {Γ : Ctx} {I I' e q j E : Tm} {l l' : Lvl} : l.Equiv l' →
      DescEq ⟨[Γ ⊢ .desc l' I' ∶ .sort l'.succ.succ, Γ ⊢ e ∶ .eqTy (.desc l I) (.desc l' I'), Γ ⊢ .drec q j E ∶ .desc l I],
        Γ ⊢ .cast (.desc l I) (.desc l' I') e (.drec q j E)
          ⟶ .drec q (.cast I I' e j) (.cast (.desc l I) (.desc l' I') e E) ∶ .desc l' I'⟩
  | castHrec {Γ : Ctx} {I I' e q H j E : Tm} {l l' : Lvl} : l.Equiv l' →
      DescEq ⟨[Γ ⊢ .desc l' I' ∶ .sort l'.succ.succ, Γ ⊢ e ∶ .eqTy (.desc l I) (.desc l' I'), Γ ⊢ .dhrec q H j E ∶ .desc l I],
        Γ ⊢ .cast (.desc l I) (.desc l' I') e (.dhrec q H j E) ⟶ Tm.castDescHrec l l' I I' e q H j E ∶ .desc l' I'⟩
  -- the cast of a constructor between two `μ`
  | castMu {Γ : Ctx} {I D i I' D' i' e x : Tm} {l l' : Lvl} : l.Equiv l' →
      DescEq ⟨[Γ ⊢ .mu l' I' D' i' ∶ .sort l'.succ, Γ ⊢ e ∶ .eqTy (.mu l I D i) (.mu l' I' D' i'), Γ ⊢ .con x ∶ .mu l I D i],
        Γ ⊢ .cast (.mu l I D i) (.mu l' I' D' i') e (.con x) ⟶ Tm.castMuCon l l' I D i I' D' i' e x ∶ .mu l' I' D' i'⟩
  /-- a cast at `Desc` or `μ` looks at its argument's head -/
  | castRedArg {Γ : Ctx} {A B e t t' : Tm} {l : Lvl} : (A.former? = some .desc ∨ A.former? = some .mu) →
      DescEq ⟨[Γ ⊢ B ∶ .sort l, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ⟶ t' ∶ A], Γ ⊢ .cast A B e t ⟶ .cast A B e t' ∶ B⟩

end WizMeta.Spec
