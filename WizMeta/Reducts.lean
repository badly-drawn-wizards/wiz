import WizMeta.Templates

/-!
# The right-hand sides of the computation rules

Each computation rule of observational equality builds a term with binders. They are
written once, here, and used both by the rules (`WizMeta/Spec/`) and by the reference
checker (`WizMeta/Checker.lean`), so that the two cannot drift apart in an index.

All arguments are terms over the context `Γ` of the redex, except a codomain `B`, which
is over `Γ, x`.
-/

namespace WizMeta
namespace Tm

def True' : Tm := .unit 0
def False' : Tm := .empty 0

/-- `(0 _ : a → b) × (b → a)`: what an equation between two propositions means. -/
def iff (a b : Tm) : Tm :=
  .sigma .zero (some 0) (.pi .zero (some 0) a b.shift) (.pi .zero (some 0) b.shift (a.shiftN 2))

/-- `B` moved under `n` more variables below its own (its variable stays `var 0`). -/
def under (n : Nat) (B : Tm) : Tm := B.ren (upRen (· + n))

/-- funext: `f =_{(x : A) → B} g  ⟶  (0 x : A) → f x =_{B} g x`. -/
def eqPi (A B f g : Tm) : Tm :=
  .pi .zero (some 0) A (.eq B (.app f.shift (.var 0)) (.app g.shift (.var 0)))

/-- The proof that `B a.1 ≡ B b.1`, from `e : a.1 = b.1` (`e` is `var 0`; the result is over
`Γ, e`): `transp A a.1 (λy _. B a.1 ≡ B y) (reflTy (B a.1)) b.1 e`. -/
def eqSigmaTransport (A B a b : Tm) : Tm :=
  let a1 : Tm := .fst a
  let b1 : Tm := .fst b
  let Ba := B.inst a1
  let P : Tm := .lam (.lam (.eqTy (Ba.shiftN 2) ((B.under 2).inst (.var 1))))
  .transp A.shift a1.shift P.shift (.reflTy Ba.shift) b1.shift (.var 0)

/-- `a =_{(x : A) × B} b  ⟶  (0 e : a.1 =_A b.1) × (cast (B a.1) (B b.1) ê a.2 =_{B b.1} b.2)`. -/
def eqSigma (A B a b : Tm) : Tm :=
  let Ba := B.inst (.fst a)
  let Bb := B.inst (.fst b)
  .sigma .zero (some 0) (.eq A (.fst a) (.fst b))
    (.eq Bb.shift (.cast Ba.shift Bb.shift (eqSigmaTransport A B a b) (Tm.snd a).shift) (Tm.snd b).shift)

/-- `((x : A₁) → B₁) ≡ ((x : A₂) → B₂)  ⟶  (0 e : A₂ ≡ A₁) × ((0 x : A₂) → B₁ (cast A₂ A₁ e x) ≡ B₂ x)`:
the domain equation is backwards, as in CCobs. -/
def eqTyPi (A₁ B₁ A₂ B₂ : Tm) : Tm :=
  let c : Tm := .cast (A₂.shiftN 2) (A₁.shiftN 2) (.var 1) (.var 0)
  .sigma .zero (some 0) (.eqTy A₂ A₁)
    (.pi .zero (some 0) A₂.shift (.eqTy ((B₁.under 2).inst c) (B₂.under 1)))

/-- `((x : A₁) × B₁) ≡ ((x : A₂) × B₂)  ⟶  (0 e : A₁ ≡ A₂) × ((0 x : A₁) → B₁ x ≡ B₂ (cast A₁ A₂ e x))`. -/
def eqTySigma (A₁ B₁ A₂ B₂ : Tm) : Tm :=
  let c : Tm := .cast (A₁.shiftN 2) (A₂.shiftN 2) (.var 1) (.var 0)
  .sigma .zero (some 0) (.eqTy A₁ A₂)
    (.pi .zero (some 0) A₁.shift (.eqTy (B₁.under 1) ((B₂.under 2).inst c)))

/-- `cast ((x : A₁) → B₁) ((x : A₂) → B₂) e t  ⟶  λx. cast (B₁ x̂) (B₂ x) (e.2 x) (t x̂)`,
`x̂ = cast A₂ A₁ e.1 x`. -/
def castPi (A₁ B₁ A₂ B₂ e t : Tm) : Tm :=
  let x' : Tm := .cast A₂.shift A₁.shift (.fst e.shift) (.var 0)
  .lam (.cast ((B₁.under 1).inst x') B₂ (.app (.snd e.shift) (.var 0)) (.app t.shift x'))

/-- `cast ((x : A₁) × B₁) ((x : A₂) × B₂) e t  ⟶  (c₁, cast (B₁ t.1) (B₂ c₁) (e.2 t.1) t.2)`,
`c₁ = cast A₁ A₂ e.1 t.1`. -/
def castSigma (A₁ B₁ A₂ B₂ e t : Tm) : Tm :=
  let t1 : Tm := .fst t
  let c1 : Tm := .cast A₁ A₂ (.fst e) t1
  .pair c1 (.cast (B₁.inst t1) (B₂.inst c1) (.app (.snd e) t1) (.snd t))

/-- The canonical type formers: two different ones are never equal. -/
inductive Former where
  | pi | sigma | sort | unit | empty | enum | ulift | desc | mu
  deriving BEq, DecidableEq, Repr

def former? : Tm → Option Former
  | .pi .. => some .pi
  | .sigma .. => some .sigma
  | .sort _ => some .sort
  | .unit _ => some .unit
  | .empty _ => some .empty
  | .enum _ => some .enum
  | .ulift .. => some .ulift
  | .desc .. => some .desc
  | .mu .. => some .mu
  | _ => none

/-! ## Descriptions -/

/-- `⟦ret j⟧ X i = (0 _ : j =_I i) × Unit` -/
def interpRet (l : Lvl) (I j i : Tm) : Tm := .sigma .zero (some l.succ) (.eq I j i) (.unit l.succ)
/-- `⟦arg q S D⟧ X i = (q s : S) × ⟦D s⟧ X i` -/
def interpArg (l : Lvl) (q : Q) (I S D X i : Tm) : Tm :=
  .sigma q (some l.succ) S (.interp l I.shift (.app D.shift (.var 0)) X.shift i.shift)
/-- `⟦rec q j D⟧ X i = (q _ : X j) × ⟦D⟧ X i` -/
def interpRec (l : Lvl) (q : Q) (I j D X i : Tm) : Tm :=
  .sigma q (some l.succ) (.app X j) (.interp l I.shift D.shift X.shift i.shift)
/-- `⟦hrec q H j D⟧ X i = (q _ : (h : H) → X (j h)) × ⟦D⟧ X i` -/
def interpHrec (l : Lvl) (q : Q) (I H j D X i : Tm) : Tm :=
  .sigma q (some l.succ) (.pi .many (some l.succ) H (.app X.shift (.app j.shift (.var 0))))
    (.interp l I.shift D.shift X.shift i.shift)

/-- The sort of `All D X P i xs`. -/
def allSort (l v : Lvl) : Lvl := .max l.succ v

/-- `All (arg q S D) X P i xs = All (D xs.1) X P i xs.2` -/
def allArg (l v : Lvl) (I D X P i xs : Tm) : Tm := .dall l v I (.app D (.fst xs)) X P i (.snd xs)
/-- `All (rec q j D) X P i xs = P j xs.1 × All D X P i xs.2` -/
def allRec (l v : Lvl) (I j D X P i xs : Tm) : Tm :=
  .sigma .many (some (allSort l v)) (apps P [j, .fst xs])
    (.dall l v I.shift D.shift X.shift P.shift i.shift (Tm.snd xs).shift)
/-- `All (hrec q H j D) X P i xs = ((h : H) → P (j h) (xs.1 h)) × All D X P i xs.2` -/
def allHrec (l v : Lvl) (I H j D X P i xs : Tm) : Tm :=
  .sigma .many (some (allSort l v))
    (.pi .many (some (.imax l.succ v)) H (apps P.shift [.app j.shift (.var 0), .app (Tm.fst xs).shift (.var 0)]))
    (.dall l v I.shift D.shift X.shift P.shift i.shift (Tm.snd xs).shift)

/-- `hyps (arg q S D) … xs = hyps (D xs.1) … xs.2` -/
def hypsArg (l v : Lvl) (I D X P f i xs : Tm) : Tm := .dhyps l v I (.app D (.fst xs)) X P f i (.snd xs)
/-- `hyps (rec q j D) … xs = (f j xs.1, hyps D … xs.2)` -/
def hypsRec (l v : Lvl) (I j D X P f i xs : Tm) : Tm :=
  .pair (apps f [j, .fst xs]) (.dhyps l v I D X P f i (.snd xs))
/-- `hyps (hrec q H j D) … xs = (λh. f (j h) (xs.1 h), hyps D … xs.2)` -/
def hypsHrec (l v : Lvl) (I j D X P f i xs : Tm) : Tm :=
  .pair (.lam (apps f.shift [.app j.shift (.var 0), .app (Tm.fst xs).shift (.var 0)]))
    (.dhyps l v I D X P f i (.snd xs))

/-- `Desc.elim P m… (arg q S D)  ⟶  marg q S D (λs. Desc.elim P m… (D s))` -/
def delimArg (v : Lvl) (P mret marg mrec mhrec q S D : Tm) : Tm :=
  apps marg [q, S, D,
    .lam (.delim v P.shift mret.shift marg.shift mrec.shift mhrec.shift (.app D.shift (.var 0)))]
/-- `Desc.elim P m… (rec q j D)  ⟶  mrec q j D (Desc.elim P m… D)` -/
def delimRec (v : Lvl) (P mret marg mrec mhrec q j D : Tm) : Tm :=
  apps mrec [q, j, D, .delim v P mret marg mrec mhrec D]
/-- `Desc.elim P m… (hrec q H j D)  ⟶  mhrec q H j D (Desc.elim P m… D)` -/
def delimHrec (v : Lvl) (P mret marg mrec mhrec q H j D : Tm) : Tm :=
  apps mhrec [q, H, j, D, .delim v P mret marg mrec mhrec D]

/-- `ind P m i (con xs)  ⟶  m i xs (hyps D (μ D) P (λj y. ind P m j y) i xs)` -/
def indCon (l v : Lvl) (I D P m i xs : Tm) : Tm := apps m [i, xs, indHyps l v I D P m i xs]

/-- The type of the function field of `hrec`: `(h : H) → X (j h)`. -/
def hrecFieldTy (l : Lvl) (H j X : Tm) : Tm :=
  .pi .many (some l.succ) H (.app X.shift (.app j.shift (.var 0)))

/-- The type of the continuation of `arg`: `(s : S) → Desc I`. -/
def argContTy (l : Lvl) (I S : Tm) : Tm := .pi .many (some l.succ.succ) S (.desc l I.shift)
/-- The type of the index function of `hrec`: `(h : H) → I`. -/
def hrecIndexTy (l : Lvl) (I H : Tm) : Tm := .pi .many (some l.succ) H I.shift
/-- The type of a family over the index type: `(i : I) → Sort (l+1)`. -/
def familyTy (l : Lvl) (I : Tm) : Tm := .pi .many (some l.succ.succ) I (.sort l.succ)
/-- The type of `transp`'s motive for `A : Sort l`: `(0 b : A) → (0 _ : a =_A b) → Prop`.
The inner `Π` is in `Sort (imax 0 1) = Sort 1`, the outer one in `Sort (imax l 1)`. -/
def transpMotiveTy (l : Lvl) (A a : Tm) : Tm :=
  .pi .zero (some (.imax l 1)) A (.pi .zero (some 1) (.eq A.shift a.shift (.var 0)) (.sort 0))

end Tm

/-- `Sort u ≡ Sort w` and the like: `True` for equal levels, `False` for two different
closed levels, stuck (`none`) otherwise: the answer must survive a level substitution. -/
def eqLevels? (u w : Lvl) : Option Tm :=
  if u.equiv w then some Tm.True'
  else if u.toNat?.isSome && w.toNat?.isSome then some Tm.False'
  else none

end WizMeta
