import WizMeta.Syntax

/-!
# The types the rules for descriptions build

The motive and method types of `Desc.elim` and `ind`, and the generic operations `All`
and `hyps` (closed `Desc.elim` terms, as in the kernel's `Templates.lean`), written with
every sort annotation. `⟦D⟧ X i` is the former `Tm.interp` (see `Syntax.lean`), with its
own rules.

Each template is written over a small context of named parameters and then closed
(`Tm.close`); the comments give that context, innermost first (`xs0 i1` means `xs` is
`var 0`, `i` is `var 1`).

Nothing here is proved well typed. `Tests/Meta.lean` checks `allTm` and `hypsTm` with the
reference checker at several levels.
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
    (.imax i j, .pi q (some (.imax i j)) A B)

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

/-- `fun j => μ D j`, the family a constructor's recursive fields live in. -/
def muFamily (l : Lvl) (I D : Tm) : Tm := .lam (.mu l I.shift D.shift (v 0))

/-- `(i : I) → (_ : μ D i) → Sort v`, the type of `ind`'s motive. -/
def indMotiveTy (l v' : Lvl) (I D : Tm) : Tm :=
  -- i0 D1 I2 ; x0 i1 D2 I3
  (pis [(ω, l.succ, v 1), (ω, l.succ, .mu l (v 2) (v 1) (v 0))] (v'.succ, .sort v')).2.close [D, I]

/-- `fun I D X P i xs => All D X P i xs`: one `P`-proof per recursive field of the payload
`xs : ⟦D⟧ X i`. In `Sort (max (l+1) v)`. -/
def allTm (l v' : Lvl) : Tm :=
  let l1 := l.succ
  let r := Lvl.max l1 v'
  -- E0 D1 I2, then X, P, i, xs
  let mot := Tm.lam (pis [
      (ω, .imax l1 l1.succ, (pis [(ω, l1, v 2)] (l1.succ, .sort l1)).2),
      (ω, .imax l1 (.imax l1 v'.succ), (pis [(ω, l1, v 3), (ω, l1, .app (v 1) (v 0))] (v'.succ, .sort v')).2),
      (ω, l1, v 4),
      (ω, l1, .interp l (v 5) (v 3) (v 2) (v 0))]
    (r.succ, .sort r)).2
  let mret := lams 5 (.unit r)
  -- xs0 i1 P2 X3 ih4 E5 S6 q7
  let marg := lams 8 (apps (v 4) [.fst (v 0), v 3, v 2, v 1, .snd (v 0)])
  -- xs0 i1 P2 X3 ih4 E5 j6 q7
  let mrec := lams 8 (.sigma ω (some r) (apps (v 2) [v 6, .fst (v 0)]) (apps (v 5) [v 4, v 3, v 2, .snd (v 1)]))
  -- xs0 i1 P2 X3 ih4 E5 j6 H7 q8
  let mhrec := lams 9 (.sigma ω (some r)
    (pis [(ω, l1, v 7)] (v', apps (v 3) [.app (v 7) (v 0), .app (.fst (v 1)) (v 0)])).2
    (apps (v 5) [v 4, v 3, v 2, .snd (v 1)]))
  lams 2 (.delim (.max l1.succ v'.succ) mot mret marg mrec mhrec (v 0))

/-- The type of `allTm`. -/
def allTy (l v' : Lvl) : Tm :=
  let l1 := l.succ
  let r := Lvl.max l1 v'
  -- I0 ; D0 I1 ; X0 D1 I2 ; P0 X1 D2 I3 ; i0 P1 X2 D3 I4 ; xs0 i1 P2 X3 D4 I5
  (pis [(ω, l1.succ, .sort l1), (ω, l1.succ, .desc l (v 0)),
      (ω, .imax l1 l1.succ, (pis [(ω, l1, v 1)] (l1.succ, .sort l1)).2),
      (ω, .imax l1 (.imax l1 v'.succ), (pis [(ω, l1, v 2), (ω, l1, .app (v 1) (v 0))] (v'.succ, .sort v')).2),
      (ω, l1, v 3),
      (ω, l1, .interp l (v 4) (v 3) (v 2) (v 0))]
    (r.succ, .sort r)).2

/-- `fun I D X P f i xs => hyps …`: `f` applied to every recursive field, a proof of
`All D X P i xs`. -/
def hypsTm (l v' : Lvl) : Tm :=
  let l1 := l.succ
  let r := Lvl.max l1 v'
  -- E0 D1 I2, then X, P, f, i, xs
  let mot := Tm.lam (pis [
      (ω, .imax l1 l1.succ, (pis [(ω, l1, v 2)] (l1.succ, .sort l1)).2),
      (ω, .imax l1 (.imax l1 v'.succ), (pis [(ω, l1, v 3), (ω, l1, .app (v 1) (v 0))] (v'.succ, .sort v')).2),
      (ω, .imax l1 (.imax l1 v'), (pis [(ω, l1, v 4), (ω, l1, .app (v 2) (v 0))] (v', apps (v 2) [v 1, v 0])).2),
      (ω, l1, v 5),
      (ω, l1, .interp l (v 6) (v 4) (v 3) (v 0))]
    (r, apps (allTm l v') [v 7, v 5, v 4, v 3, v 1, v 0])).2
  let mret := lams 6 .tt
  -- xs0 i1 f2 P3 X4 ih5 E6 S7 q8
  let marg := lams 9 (apps (v 5) [.fst (v 0), v 4, v 3, v 2, v 1, .snd (v 0)])
  -- xs0 i1 f2 P3 X4 ih5 E6 j7 q8
  let mrec := lams 9 (.pair (apps (v 2) [v 7, .fst (v 0)]) (apps (v 5) [v 4, v 3, v 2, v 1, .snd (v 0)]))
  -- xs0 i1 f2 P3 X4 ih5 E6 j7 H8 q9
  let mhrec := lams 10 (.pair (.lam (apps (v 3) [.app (v 8) (v 0), .app (.fst (v 1)) (v 0)]))
    (apps (v 5) [v 4, v 3, v 2, v 1, .snd (v 0)]))
  lams 2 (.delim (.max l1.succ v'.succ) mot mret marg mrec mhrec (v 0))

/-- The type of `hypsTm`. -/
def hypsTy (l v' : Lvl) : Tm :=
  let l1 := l.succ
  let r := Lvl.max l1 v'
  -- I0 ; D0 I1 ; X0 D1 I2 ; P0 X1 D2 I3 ; f0 P1 X2 D3 I4 ; i0 f1 P2 X3 D4 I5 ; xs0 i1 f2 P3 X4 D5 I6
  (pis [(ω, l1.succ, .sort l1), (ω, l1.succ, .desc l (v 0)),
      (ω, .imax l1 l1.succ, (pis [(ω, l1, v 1)] (l1.succ, .sort l1)).2),
      (ω, .imax l1 (.imax l1 v'.succ), (pis [(ω, l1, v 2), (ω, l1, .app (v 1) (v 0))] (v'.succ, .sort v')).2),
      (ω, .imax l1 (.imax l1 v'), (pis [(ω, l1, v 3), (ω, l1, .app (v 2) (v 0))] (v', apps (v 2) [v 1, v 0])).2),
      (ω, l1, v 4),
      (ω, l1, .interp l (v 5) (v 4) (v 3) (v 0))]
    (r, apps (allTm l v') [v 6, v 5, v 4, v 3, v 1, v 0])).2

/-- `(0 i : I) → (xs : ⟦D⟧ (μ D) i) → (ih : All D (μ D) P i xs) → P i (con xs)`, the type of
`ind`'s method. -/
def indMethodTy (l v' : Lvl) (I D P : Tm) : Tm :=
  let l1 := l.succ
  -- i0 P1 D2 I3 ; xs0 i1 P2 D3 I4 ; ih0 xs1 i2 P3 D4 I5
  (pis [(.zero, l1, v 2),
      (ω, l1, .interp l (v 3) (v 2) (muFamily l (v 3) (v 2)) (v 0)),
      (ω, .max l1 v', apps (allTm l v') [v 4, v 3, muFamily l (v 4) (v 3), v 2, v 1, v 0])]
    (v', apps (v 3) [v 2, .con (v 1)])).2.close [P, D, I]

/-- The induction hypotheses of `ind P m i (con xs)`. -/
def indHyps (l v' : Lvl) (I D P m i xs : Tm) : Tm :=
  let f : Tm := .lam (.lam (.ind l (I.shiftN 2) (D.shiftN 2) v' (P.shiftN 2) (m.shiftN 2) (v 1) (v 0)))
  apps (hypsTm l v') [I, D, muFamily l I D, P, f, i, xs]

end Tm
end WizMeta
