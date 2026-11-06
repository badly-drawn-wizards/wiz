import Wiz.Elab.Unify

/-!
# Zonking

Before a declaration goes to the kernel, every solved metavariable is replaced by its
solution ("zonking", a GHC term). A solved meta applied to arguments,
`?m a₁ … aₙ`, is evaluated and quoted back, which β-reduces the solution's lambdas
away. That matters: the kernel can't infer a type for `(fun x => …) a`.
-/

namespace Wiz

variable {R : Type} [Zero R] [DecidableEq R]

/-- **Exercise 3.6.** Replace solved metas in `t`, a term in a context of `l` variables.

Split `t` into a head and arguments. If the head is a *solved* meta, evaluate
`solution a₁ … aₙ` (arguments evaluated in the environment of variables
`[Val.var (l-1), …, Val.var 0]`), quote the result back at `l`, and zonk *that*, since
solutions can mention metas solved later. Otherwise rebuild the term, zonking every
subterm (under binders at `l + 1`) and instantiating level metas in `sort` and
`const` (`instLevel`). Unsolved metas stay. -/
partial def zonk (l : Lvl) (t : Term R) : ElabM R (Term R) := do
  sorry

/-- The metavariables still occurring in a term. -/
partial def Term.mvars : Term R → Array Nat
  | .mvar m => #[m]
  | .pi _ _ _ a b | .app a b | .ann a b => a.mvars ++ b.mvars
  | .lam _ b => b.mvars
  | .letE _ _ ty v b => ty.mvars ++ v.mvars ++ b.mvars
  | .sigma _ _ a b | .pair a b | .absurd a b => a.mvars ++ b.mvars
  | .fst t | .snd t => t.mvars
  | .split _ s _ m _ _ b => s.mvars ++ m.mvars ++ b.mvars
  | .eq A a b => A.mvars ++ a.mvars ++ b.mvars
  | .eqTy A B | .refl A B => A.mvars ++ B.mvars
  | .reflTy X => X.mvars
  | .cast A B e t => A.mvars ++ B.mvars ++ e.mvars ++ t.mvars
  | .transp A a P p b e => A.mvars ++ a.mvars ++ P.mvars ++ p.mvars ++ b.mvars ++ e.mvars
  | _ => #[]

/-- Does the term mention a level metavariable? -/
partial def Term.hasLevelMVar : Term R → Bool
  | .sort l => l.hasMVar
  | .const _ us => us.any Level.hasMVar
  | .pi _ _ _ a b | .app a b | .ann a b => a.hasLevelMVar || b.hasLevelMVar
  | .lam _ b => b.hasLevelMVar
  | .letE _ _ ty v b => ty.hasLevelMVar || v.hasLevelMVar || b.hasLevelMVar
  | .sigma _ _ a b | .pair a b | .absurd a b => a.hasLevelMVar || b.hasLevelMVar
  | .fst t | .snd t => t.hasLevelMVar
  | .split _ s _ m _ _ b => s.hasLevelMVar || m.hasLevelMVar || b.hasLevelMVar
  | .unit l | .empty l => l.hasMVar
  | .eq A a b => A.hasLevelMVar || a.hasLevelMVar || b.hasLevelMVar
  | .eqTy A B | .refl A B => A.hasLevelMVar || B.hasLevelMVar
  | .reflTy X => X.hasLevelMVar
  | .cast A B e t => [A, B, e, t].any Term.hasLevelMVar
  | .transp A a P p b e => [A, a, P, p, b, e].any Term.hasLevelMVar
  | _ => false

/-- Fail if `t` still contains unsolved metas, pointing at the first one's hole. -/
def ensureNoMVars (t : Term R) (info : SourceInfo := {}) : ElabM R Unit := do
  if let some m := t.mvars[0]? then
    let e ← lookupMeta m
    throwAt e.info s!"could not infer {e.desc}"
  if t.hasLevelMVar then
    throwAt info "could not infer a universe level; add a universe parameter or annotation"

end Wiz
