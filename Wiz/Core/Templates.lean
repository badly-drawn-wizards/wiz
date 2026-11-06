import Wiz.Core.Term
import Wiz.Rig

/-!
# Description templates

The generic operations on descriptions are **closed terms built with `Desc.elim`**,
not kernel primitives. The kernel evaluates them like any other term, and on a
neutral description they get stuck as an ordinary `Desc.elim` elimination.

    ⟦ret j⟧ X i      = (0 _ : j = i) × Unit          ⟦arg q S D⟧ X i = (%q s : S) × ⟦D s⟧ X i
                                                     ⟦rec q j D⟧ X i = (%q _ : X j) × ⟦D⟧ X i
    All (ret j) …    = Unit                          All (arg …) P i xs = All (D xs.1) P i xs.2
                                                     All (rec …) P i xs = P j xs.1 × All D P i xs.2
    hyps / map       : the same recursion, building the hypotheses / mapping `f` over recursive fields

Each template takes `I D` first, then the operation's own arguments. Comments give the
de Bruijn context, innermost first (`xs0 i1 …` means `xs` is `var 0`, `i` is `var 1`,
…).

**Exercise 4.17** (optional, but instructive): write `allTm` yourself from the table,
following `interpTm`.
-/

namespace Wiz.Templates

variable {R : Type} [QRig R] [QuantitySyntax R]

private def v (i : Nat) : Term R := .var i
private def apps (f : Term R) (as : List (Term R)) : Term R := as.foldl .app f
private def lams (xs : List Name) (b : Term R) : Term R := xs.foldr .lam b
/-- Binders inside templates are unrestricted: the rig's default quantity. -/
private def pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit QuantitySyntax.explicitDefault) a b

/-- `fun I D X i => ⟦D⟧ X i` for `D : Desc.{l} I`. -/
def interpTm (l : Level) : Term R :=
  let tyL : Term R := .sort (.succ l)
  -- ctx: D0 I1
  let P := .lam "_" (pi "X" (pi "_" (v 2) tyL) (pi "i" (v 3) tyL))
  -- i0 X1 j2 D3 I4
  let mret := lams ["j", "X", "i"] (.sigma "_" (.qlit 0) (.eq (v 4) (v 2) (v 0)) (.unit (.succ l)))
  -- i0 X1 ih2 E3 S4 q5
  let marg := lams ["q", "S", "E", "ih", "X", "i"] (.sigma "s" (v 5) (v 4) (apps (v 3) [v 0, v 2, v 1]))
  -- i0 X1 ih2 E3 j4 q5
  let mrec := lams ["q", "j", "E", "ih", "X", "i"] (.sigma "_" (v 5) (.app (v 1) (v 4)) (apps (v 3) [v 2, v 1]))
  lams ["I", "D"] (.delim (.succ (.succ l)) P mret marg mrec (v 0))

private def interpApp (l : Level) (I E X i : Term R) : Term R := apps (interpTm l) [I, E, X, i]

/-- `fun I D X P i xs => All D X P i xs`: one `P`-proof per recursive field. -/
def allTm (l v' : Level) : Term R :=
  sorry

/-- `fun I D X P f i xs => hyps …`: apply `f` to every recursive field. -/
def hypsTm (l v' : Level) : Term R :=
  let tyL : Term R := .sort (.succ l)
  let allApp (I E X P i xs : Term R) : Term R := apps (allTm l v') [I, E, X, P, i, xs]
  -- E0 D1 I2, then X, P, f, i, xs
  let P := .lam "E" (pi "X" (pi "_" (v 2) tyL)
    (pi "P" (pi "i" (v 3) (pi "_" (.app (v 1) (v 0)) (.sort v')))
      (pi "f" (pi "i" (v 4) (pi "x" (.app (v 2) (v 0)) (apps (v 2) [v 1, v 0])))
        (pi "i" (v 5) (pi "xs" (interpApp l (v 6) (v 4) (v 3) (v 0)) (allApp (v 7) (v 5) (v 4) (v 3) (v 1) (v 0)))))))
  let mret := lams ["j", "X", "P", "f", "i", "xs"] .tt
  -- xs0 i1 f2 P3 X4 ih5 E6 S7 q8
  let marg := lams ["q", "S", "E", "ih", "X", "P", "f", "i", "xs"] (apps (v 5) [.fst (v 0), v 4, v 3, v 2, v 1, .snd (v 0)])
  -- xs0 i1 f2 P3 X4 ih5 E6 j7 q8
  let mrec := lams ["q", "j", "E", "ih", "X", "P", "f", "i", "xs"]
    (.pair (apps (v 2) [v 7, .fst (v 0)]) (apps (v 5) [v 4, v 3, v 2, v 1, .snd (v 0)]))
  lams ["I", "D"] (.delim (.max (.succ (.succ l)) (.succ v')) P mret marg mrec (v 0))

/-- `fun I D X Y f i xs => map …`: apply `f` to every recursive field. -/
def mapTm (l : Level) : Term R :=
  let tyL : Term R := .sort (.succ l)
  -- E0 D1 I2, then X, Y, f, i, xs
  let P := .lam "E" (pi "X" (pi "_" (v 2) tyL) (pi "Y" (pi "_" (v 3) tyL)
    (pi "f" (pi "i" (v 4) (pi "_" (.app (v 2) (v 0)) (.app (v 2) (v 1))))
      (pi "i" (v 5) (pi "xs" (interpApp l (v 6) (v 4) (v 3) (v 0)) (interpApp l (v 7) (v 5) (v 3) (v 1)))))))
  let mret := lams ["j", "X", "Y", "f", "i", "xs"] (v 0)
  -- xs0 i1 f2 Y3 X4 ih5 E6 S7 q8
  let marg := lams ["q", "S", "E", "ih", "X", "Y", "f", "i", "xs"]
    (.pair (.fst (v 0)) (apps (v 5) [.fst (v 0), v 4, v 3, v 2, v 1, .snd (v 0)]))
  -- xs0 i1 f2 Y3 X4 ih5 E6 j7 q8
  let mrec := lams ["q", "j", "E", "ih", "X", "Y", "f", "i", "xs"]
    (.pair (apps (v 2) [v 7, .fst (v 0)]) (apps (v 5) [v 4, v 3, v 2, v 1, .snd (v 0)]))
  lams ["I", "D"] (.delim (.succ (.succ l)) P mret marg mrec (v 0))

end Wiz.Templates
