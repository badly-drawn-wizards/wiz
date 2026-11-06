import Wiz.Elab.Unify

/-!
# Zonking

Before a declaration goes to the kernel, every solved metavariable is replaced by its
solution ("zonking", a GHC term). A solved meta applied to arguments,
`?m a₁ … aₙ`, is evaluated and quoted back, which β-reduces the solution's lambdas
away. That matters: the kernel can't infer a type for `(fun x => …) a`.
-/

namespace Wiz

variable {R : Type}

/-- **Exercise 3.6.** Replace solved metas in `t`, a term in a context of `l` variables.

Split `t` into a head and arguments. If the head is a *solved* meta, evaluate
`solution a₁ … aₙ` (arguments evaluated in the environment of variables
`[Val.var (l-1), …, Val.var 0]`), quote the result back at `l`, and zonk *that*, since
solutions can mention metas solved later. Otherwise rebuild the term, zonking every
subterm (under binders at `l + 1`). Unsolved metas stay. -/
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
      | .pi x bi q a b => return .pi x bi q (← zonk l a) (← zonk (l + 1) b)
      | .lam x b => return .lam x (← zonk (l + 1) b)
      | .letE x q ty v b => return .letE x q (← zonk l ty) (← zonk l v) (← zonk (l + 1) b)
      | .ann tm ty => return .ann (← zonk l tm) (← zonk l ty)
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
  | _ => #[]

/-- Fail if `t` still contains unsolved metas, pointing at the first one's hole. -/
def ensureNoMVars (t : Term R) : ElabM R Unit := do
  if let some m := t.mvars[0]? then
    let e ← lookupMeta m
    throwAt e.info s!"could not infer {e.desc}"

end Wiz
