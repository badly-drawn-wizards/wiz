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
    let h' ← h.mapChildrenM instLevel (fun k c => zonk (l + k) c)
    -- a `Π`/`Σ`'s (or a `ULift`'s) sort that stays unknown becomes a hole, which the sorts
    -- pass fills before the kernel (`Decl.withSorts`)
    let unknown (k : Level) : Level := if k.hasMVar then .hole else k
    let h' := match h' with
      | .pi x bi q a b σ => .pi x bi q a b ⟨unknown σ.dom, unknown σ.cod⟩
      | .sigma x q a b σ => .sigma x q a b ⟨unknown σ.dom, unknown σ.cod⟩
      | .ulift k l a => .ulift (unknown k) l a
      | _ => h'
    return (← args.mapM (zonk l)).foldl .app h'
where
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)
  --|ex
  --| sorry
  --sol>

/-- (7e) Replace only the solved *instance* holes in `t` (`MetaEntry.isInst`), leaving
every other hole as it is. The declared type of a `def` gets this before its body is
checked: the kernel's native arithmetic can't see through a solved instance hole, while
zonking the rest (the implicit arguments, say `Lens.GetPut ?S ?A l`) would let the
type's equation compute further than as written (to a Σ of field equations at a
structure), and `rfl` would then be proved field by field instead of as `refl` of its
sides. -/
partial def zonkInsts (l : Lvl) (t : Term R) : ElabM R (Term R) := do
  let (h, args) := spine t #[]
  match h with
  | .mvar m =>
    let e ← lookupMeta m
    match e.solution, e.isInst with
    | some sol, true =>
      let g ← getGlobals
      let env : Env R := ((List.range l).map fun i => Val.var i).reverse
      let v := args.foldl (fun f a => vApp g f (eval g env a)) sol
      zonkInsts l (quote g l v)
    | _, _ => return (← args.mapM (zonkInsts l)).foldl .app (.mvar m)
  | _ =>
    let h' ← h.mapChildrenM pure (fun k c => zonkInsts (l + k) c)
    return (← args.mapM (zonkInsts l)).foldl .app h'
where
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)

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
