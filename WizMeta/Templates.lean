import WizMeta.Syntax

/-!
# The types the rules for descriptions build

The motive and method types of `Desc.elim` and `ind`, written with every sort annotation.
Each is written over a small context of named parameters and then closed (`Tm.close`);
the comments give that context, innermost first (`xs0 i1` means `xs` is `var 0`, `i` is
`var 1`).

The generic operations `⟦D⟧ X i`, `All` and `hyps` are formers of the syntax with their own
rules (`Reducts.lean`), not closed `Desc.elim` terms as in the kernel's `Templates.lean`:
those terms abstract over a field's quantity and put it on a `Σ`, which a quantity
*label* cannot express.
-/

namespace WizMeta
namespace Tm

/-- `t` is written over `env ++ Γ` (index `k < env.length` stands for `env[k]`, a term over
`Γ`); the result is a term over `Γ`. -/
def close (env : List Tm) (t : Tm) : Tm :=
  t.sub fun i => if h : i < env.length then env[i] else .var (i - env.length)

def apps (f : Tm) (as : List Tm) : Tm := as.foldl .app f

def lams : Nat → Tm → Tm
  | 0, b => b
  | n + 1, b => .lam (lams n b)

/-- A telescope of `Π`s with their sorts: each binder comes with its quantity and the
level of its domain, the codomain with its level. Returns the level of the whole. -/
def pis : List (Q × Lvl × Tm) → Lvl × Tm → Lvl × Tm
  | [], r => r
  | (q, i, A) :: bs, r =>
    let (j, B) := pis bs r
    (.imax i j, .pi q (some ⟨i, j⟩) A B)

private def v (i : Nat) : Tm := .var i
private def ω : Q := .many

/-- `(_ : Desc.{l} I) → Sort v`, the type of `Desc.elim`'s motive. -/
def delimMotiveTy (l v' : Lvl) (I : Tm) : Tm :=
  (pis [(ω, l.succ.succ, .desc l I)] (v'.succ, .sort v')).2

/-- The types of `mret`, `marg`, `mrec`, `mhrec` for `Desc.elim.{v}` with motive `P` on
descriptions in `Desc.{l} I`. -/
def delimMethodTys (l v' : Lvl) (I P : Tm) : Tm × Tm × Tm × Tm :=
  let l1 := l.succ
  let l2 := l.succ.succ
  -- i0 P1 I2
  let mret := pis [(ω, l1, v 1)] (v', .app (v 1) (.dret (v 0)))
  -- q0 P1 I2 ; S0 q1 P2 I3 ; E0 S1 q2 P3 I4 ; ih0 E1 S2 q3 P4 I5
  let marg := pis [(ω, 1, .qty), (ω, l2, .sort l1),
      (ω, l2, (pis [(ω, l1, v 0)] (l2, .desc l (v 4))).2),
      (ω, .imax l1 v', (pis [(ω, l1, v 1)] (v', .app (v 4) (.app (v 1) (v 0)))).2)]
    (v', .app (v 4) (.darg (v 3) (v 2) (v 1)))
  -- q0 P1 I2 ; j0 q1 P2 I3 ; E0 j1 q2 P3 I4 ; ih0 E1 j2 q3 P4 I5
  let mrec := pis [(ω, 1, .qty), (ω, l1, v 2), (ω, l2, .desc l (v 3)), (ω, v', .app (v 3) (v 0))]
    (v', .app (v 4) (.drec (v 3) (v 2) (v 1)))
  -- q0 P1 I2 ; H0 q1 P2 I3 ; j0 H1 q2 P3 I4 ; E0 j1 H2 q3 P4 I5 ; ih0 E1 j2 H3 q4 P5 I6
  let mhrec := pis [(ω, 1, .qty), (ω, l2, .sort l1),
      (ω, .imax l1 l1, (pis [(ω, l1, v 0)] (l1, v 4)).2),
      (ω, l2, .desc l (v 4)), (ω, v', .app (v 4) (v 0))]
    (v', .app (v 5) (.dhrec (v 4) (v 3) (v 2) (v 1)))
  let env := [P, I]
  (mret.2.close env, marg.2.close env, mrec.2.close env, mhrec.2.close env)

/-- `(fun j => μ D j : (j : I) → Sort (l+1))`, the family a constructor's recursive fields live
in. Annotated, so that the reducts that apply it (`X j` in a payload equation) are
inferable; the annotation is `familyTy` (written out: it is defined after this). -/
def muFamily (l : Lvl) (I D : Tm) : Tm :=
  .ann (.lam (.mu l I.shift D.shift (v 0))) (.pi .many (some ⟨l.succ, l.succ.succ⟩) I (.sort l.succ))

/-- `(i : I) → (_ : μ D i) → Sort v`, the type of `ind`'s motive. -/
def indMotiveTy (l v' : Lvl) (I D : Tm) : Tm :=
  -- i0 D1 I2 ; x0 i1 D2 I3
  (pis [(ω, l.succ, v 1), (ω, l.succ, .mu l (v 2) (v 1) (v 0))] (v'.succ, .sort v')).2.close [D, I]

/-- `(i : I) → (_ : X i) → Sort v`, the type of a predicate over a family `X`. -/
def predTy (l v' : Lvl) (I X : Tm) : Tm :=
  -- i0 X1 I2
  (pis [(ω, l.succ, v 1), (ω, l.succ, .app (v 1) (v 0))] (v'.succ, .sort v')).2.close [X, I]

/-- `(i : I) → (x : X i) → P i x`, the type of a section of a predicate. -/
def sectionTy (l v' : Lvl) (I X P : Tm) : Tm :=
  -- i0 P1 X2 I3 ; x0 i1 P2 X3 I4
  (pis [(ω, l.succ, v 2), (ω, l.succ, .app (v 2) (v 0))] (v', apps (v 2) [v 1, v 0])).2.close [P, X, I]

/-- `(0 i : I) → (xs : ⟦D⟧ (μ D) i) → (ih : All D (μ D) P i xs) → P i (con xs)`, the type of
`ind`'s method. -/
def indMethodTy (l v' : Lvl) (I D P : Tm) : Tm :=
  let l1 := l.succ
  -- i0 P1 D2 I3 ; xs0 i1 P2 D3 I4 ; ih0 xs1 i2 P3 D4 I5
  (pis [(.zero, l1, v 2),
      (ω, l1, .interp l (v 3) (v 2) (muFamily l (v 3) (v 2)) (v 0)),
      (ω, .max l1 v', .dall l v' (v 4) (v 3) (muFamily l (v 4) (v 3)) (v 2) (v 1) (v 0))]
    (v', apps (v 3) [v 2, .con (v 1)])).2.close [P, D, I]

/-- The induction hypotheses of `ind P m i (con xs)`. -/
def indHyps (l v' : Lvl) (I D P m i xs : Tm) : Tm :=
  let f : Tm := .lam (.lam (.ind l (I.shiftN 2) (D.shiftN 2) v' (P.shiftN 2) (m.shiftN 2) (v 1) (v 0)))
  .dhyps l v' I D (muFamily l I D) P f i xs

end Tm
end WizMeta
