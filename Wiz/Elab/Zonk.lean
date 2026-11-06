import Wiz.Elab.Unify

/-!
# Zonking

Before a declaration goes to the kernel, every solved metavariable is replaced by its
solution ("zonking", a GHC term). A solved meta applied to arguments,
`?m a₁ … aₙ`, is evaluated and quoted back, which β-reduces the solution's lambdas
away. That matters: the kernel can't infer a type for `(fun x => …) a`.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

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
partial def Term.mvars (t : Term R) : Array Nat :=
  (go t |>.run #[]).2
where
  go : Term R → StateM (Array Nat) Unit
    | .mvar m => modify (·.push m)
    | t => t.forChildren (fun _ => pure ()) (fun _ c => go c)

/-- Does the term mention a level metavariable? -/
partial def Term.hasLevelMVar (t : Term R) : Bool :=
  (go t |>.run false).2
where
  go (t : Term R) : StateM Bool Unit :=
    t.forChildren (fun l => modify (· || l.hasMVar)) (fun _ c => go c)

/-- Fail if `t` still contains unsolved metas, pointing at the first one's hole. -/
def ensureNoMVars (t : Term R) (info : SourceInfo := {}) : ElabM R Unit := do
  if let some m := t.mvars[0]? then
    let e ← lookupMeta m
    throwAt e.info s!"could not infer {e.desc}"
  if t.hasLevelMVar then
    throwAt info "could not infer a universe level; add a universe parameter or annotation"

end Wiz
