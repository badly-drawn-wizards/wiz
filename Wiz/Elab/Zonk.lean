import Wiz.Elab.Unify

/-!
# Zonking

Before a declaration goes to the kernel, every solved metavariable is replaced by its
solution ("zonking", a GHC term). A solved meta applied to arguments,
`?m a₁ … aₙ`, is evaluated and quoted back, which β-reduces the solution's lambdas
away. That matters: the kernel can't infer a type for `(fun x => …) a`.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R]

/-- **Exercise 3.6.** Replace solved metas in `t`, a term in a context of `l` variables.

Split `t` into a head and arguments. If the head is a *solved* meta, evaluate
`solution a₁ … aₙ` (arguments evaluated in the environment of variables
`[Val.var (l-1), …, Val.var 0]`), quote the result back at `l`, and zonk *that*, since
solutions can mention metas solved later. Otherwise rebuild the term, zonking every
subterm (under binders at `l + 1`) and instantiating level metas in `sort` and
`const` (`instLevel`). Unsolved metas stay. -/
partial def zonk (l : Lvl) (t : Term R) : ElabM R (Term R) := do
  --<sol
  let (h, args) := spine t #[]
  match h with
  | .mvar m =>
    match (← lookupMeta m).solution with
    | some sol =>
      let g ← getGlobals
      let env : Env R := (List.range l).map fun i => Val.var i
      let env := env.reverse
      let v := args.foldl (fun f a => vApp g f (eval g env a)) sol
      zonk l (quote g l v)
    | none => return (← args.mapM (zonk l)).foldl .app (.mvar m)
  | _ =>
    let h' ← match h with
      | .pi x bi q a b => pure (.pi x bi q (← zonk l a) (← zonk (l + 1) b))
      | .lam x b => pure (.lam x (← zonk (l + 1) b))
      | .letE x q ty v b => pure (.letE x q (← zonk l ty) (← zonk l v) (← zonk (l + 1) b))
      | .ann tm ty => pure (.ann (← zonk l tm) (← zonk l ty))
      | .sort u => pure (.sort (← instLevel u))
      | .const n us => pure (.const n (← us.mapM instLevel))
      | .sigma x q a b => pure (.sigma x q (← zonk l a) (← zonk (l + 1) b))
      | .pair a b => pure (.pair (← zonk l a) (← zonk l b))
      | .fst t => pure (.fst (← zonk l t))
      | .snd t => pure (.snd (← zonk l t))
      | .split q s z m x y b =>
        pure (.split q (← zonk l s) z (← zonk (l + 1) m) x y (← zonk (l + 2) b))
      | .unit u => pure (.unit (← instLevel u))
      | .empty u => pure (.empty (← instLevel u))
      | .absurd m t => pure (.absurd (← zonk l m) (← zonk l t))
      | .eq A a b => pure (.eq (← zonk l A) (← zonk l a) (← zonk l b))
      | .eqTy A B => pure (.eqTy (← zonk l A) (← zonk l B))
      | .refl A a => pure (.refl (← zonk l A) (← zonk l a))
      | .reflTy X => pure (.reflTy (← zonk l X))
      | .cast A B e t => pure (.cast (← zonk l A) (← zonk l B) (← zonk l e) (← zonk l t))
      | .transp A a P p b e =>
        pure (.transp (← zonk l A) (← zonk l a) (← zonk l P) (← zonk l p) (← zonk l b) (← zonk l e))
      | other => pure other
    return (← args.mapM (zonk l)).foldl .app h'
where
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)
  --|ex
  --| sorry
  --sol>

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
