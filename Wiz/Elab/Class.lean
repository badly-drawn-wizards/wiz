import Wiz.Elab.Zonk

/-!
# Type classes: tabled instance resolution

A class is a structure registered with `class`; an instance is a global registered
with `instance`, whose type is `{Δ} → [C₁ …] → … → C args`. An instance-implicit
argument `[x : C A]` becomes a hole and an **instance problem**, solved as soon as
its type is known enough, or at the end of the command.

Resolution follows Selsam, Ullrich & de Moura, *Tabled Typeclass Resolution* (2020),
the algorithm of Lean 4, in a simplified form:

* a **generator** node holds a goal and the instances still to try on it;
* applying an instance leaves its instance arguments as subgoals; a **consumer** node
  holds the subgoals still to solve, with the elaborator state of its partial solution;
* each goal, normalised to a **key** (metavariables numbered in order), has a table
  entry with its answers so far and the consumers waiting for them. A subgoal that
  is already in the table is not solved again: the consumer waits for the existing
  generator's answers, including future ones. That is what makes resolution
  terminate on cycles (`Coe A B → Coe B A → …`) and share work on diamonds.

Answers must be complete terms (no holes). Output parameters (`outParam`) are replaced
by fresh holes before resolution, so they are not part of the key, and are unified
with the answer afterwards. Instances are tried in order: local instances, then by
priority, then latest first.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

structure Answer (R : Type) where
  val : Term R
  ty : Term R

structure Consumer (R : Type) where
  /-- the key of the goal this consumer will produce answers for -/
  key : String
  goal : Term R
  goalTy : VTy R
  /-- the subgoals left: holes and their types -/
  subgoals : List (Term R × VTy R)
  state : ElabState R

structure Generator (R : Type) where
  key : String
  goal : Term R
  goalTy : VTy R
  state : ElabState R
  /-- instances to try (a term and its type), in order -/
  candidates : Array (Term R × VTy R)
  next : Nat := 0

inductive Waiter (R : Type) where
  | root
  | consumer (c : Consumer R)

structure Entry (R : Type) where
  waiters : Array (Waiter R) := #[]
  answers : Array (Answer R) := #[]

structure SynthState (R : Type) where
  gens : Array (Generator R) := #[]
  resume : Array (Consumer R × Answer R) := #[]
  table : Std.HashMap String (Entry R) := {}
  result : Option (Answer R) := none
  steps : Nat := 0

/-- A type, with solved holes filled in, for messages. -/
def showType (ctx : LocalCtx R) (ty : VTy R) : ElabM R String := do
  pure ((← zonk ctx.lvl (quote (← getGlobals) ctx.lvl ty)).pretty ctx.names)

/-- The class of a type, if it is an application of one (kept by glued evaluation). -/
def classOf? (ty : VTy R) : ElabM R (Option (ClassInfo × List Level × Array (Val R))) := do
  let .unfold n us sp _ ← forceMeta ty | return none
  let some info := (← get).classes.find? (·.name == n) | return none
  let args := sp.filterMap fun | .app a => some a | _ => none
  return some (info, us, args)

/-- Number the metavariables of a term in order of occurrence. -/
partial def canonMVars (t : Term R) : StateM (Array Nat) (Term R) := do
  match t with
  | .mvar m =>
    let ms ← get
    match ms.idxOf? m with
    | some i => pure (.mvar (1000000000 + i))
    | none => set (ms.push m); pure (.mvar (1000000000 + ms.size))
  | t => t.mapChildrenM pure (fun _ c => canonMVars c)

/-- The table key of a goal type. -/
def goalKey (ctx : LocalCtx R) (ty : VTy R) : ElabM R String := do
  let t ← zonk ctx.lvl (quote (← getGlobals) ctx.lvl ty)
  let t' : Term R := (canonMVars t).run' #[] |>.run
  pure (t'.pretty [])

/-- The instances to try on a goal of class `cls`: local instances, then global ones by
priority, latest first. -/
def candidates (ctx : LocalCtx R) (cls : Name) : ElabM R (Array (Term R × VTy R)) := do
  let mut out := #[]
  -- local instances: hypotheses whose type is an application of the class
  for j in [0:ctx.lvl] do
    if let some (info, _, _) ← classOf? ctx.types[j]! then
      if info.name == cls then out := out.push (.var j, ctx.types[j]!)
  let s ← get
  let insts := (s.instances.toList.zipIdx.filter (·.1.cls == cls)).toArray
  let sorted := insts.qsort fun (a, i) (b, j) => a.priority > b.priority || (a.priority == b.priority && i > j)
  for (inst, _) in sorted do
    if let some d := s.globals.find? inst.name then
      let us ← d.levelParams.mapM fun _ => freshLevelMeta
      out := out.push (.const inst.name us, eval s.globals [] (d.type.instLevels d.levelParams us))
  pure out

def mkGenerator (ctx : LocalCtx R) (key : String) (goal : Term R) (goalTy : VTy R) : ElabM R (Generator R) := do
  let cands ← match ← classOf? goalTy with
    | some (info, _, _) => candidates ctx info.name
    | none => pure #[]
  pure { key, goal, goalTy, state := ← get, candidates := cands }

/-- (Given) Does each complete solution of an instance's non-instance argument have the
type the instance's binder gives it? Unification is untyped, so matching the instance's
conclusion can pick an ill-kinded solution: `ShareLet (r a) (r b)` against `S T.El`
(first order: `r := S`, `a := T.El`) although `r : T → Type` and `S : (T → Type) → Type`.
Such an instance doesn't apply. (Arguments still holes, or whose types are, are left to
the rest of elaboration and the kernel.) -/
def instArgsWellTyped (ctx : LocalCtx R) (args : Array (Term R × VTy R)) : ElabM R Bool := do
  let g ← getGlobals
  let mut checks : Array (Term R × Term R) := #[]
  for (m, dom) in args do
    let t ← zonk ctx.lvl m
    if !t.mvars.isEmpty || t.hasLevelMVar then continue
    let A ← zonk ctx.lvl (quote g ctx.lvl (← forceMeta dom))
    if !A.mvars.isEmpty || A.hasLevelMVar then continue
    checks := checks.push (t, A)
  if checks.isEmpty then return true
  -- the variables' types with the holes solved since they were bound
  let mut tys : Array (VTy R) := #[]
  for v in ctx.types.reverse do
    let j := tys.size
    let t ← zonk j (quote g j (← forceMeta v))
    tys := tys.push (eval g (ctx.env.drop (ctx.lvl - j)) t)
  let kctx : Ctx R := { globals := g, env := ctx.env, names := ctx.names,
                        qtys := ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault,
                        types := tys.toList.reverse, lvl := ctx.lvl }
  let infer := (← get).kernelInfer
  for (t, A) in checks do
    match infer kctx t with
    | .ok ty => unless convTy g tys (eval g ctx.env A) ty do return false
    -- (ill-typed; unless there is no kernel to ask, outside a command)
    | .error e => if e != noKernelMsg then return false
  return true

/-- **Exercise 7.1.** Apply an instance (`e : ty`) to the goal: fill each of its leading
Π binders with a fresh hole (the instance-implicit ones are the subgoals, in order),
then unify the conclusion with the goal type and the goal with the application.
Stop at the conclusion without unfolding it (match on `forceMeta`, not `force`).
Throws if it doesn't apply. -/
partial def applyInstance (ctx : LocalCtx R) (goal : Term R) (goalTy : VTy R) (e : Term R) (ty : VTy R) :
    ElabM R (List (Term R × VTy R)) := do
  --<sol
  let mut t := e
  let mut ty := ty
  let mut subgoals := #[]
  let mut args := #[]
  repeat
    match ← forceMeta ty with
    | .pi x bi _ dom cod _ =>
      let m ← freshMeta ctx s!"instance argument {x}"
      if bi == .instImplicit then subgoals := subgoals.push (m, dom) else args := args.push (m, dom)
      t := .app t m
      ty ← instM cod (← evalIn ctx m)
    | _ => break
  unify ctx.lvl goalTy ty
  unless ← instArgsWellTyped ctx args do throwAt {} "instance does not apply: an ill-typed argument"
  unify ctx.lvl (← evalIn ctx goal) (← evalIn ctx t)
  pure subgoals.toList
  --|ex
  --| sorry
  --sol>

/-- Tabled resolution of `ty` in `ctx`: a complete term of that type, or `none`. -/
partial def synthInstance (ctx : LocalCtx R) (ty : VTy R) : ElabM R (Option (Term R)) := do
  let some (info, us, args) ← classOf? ty | return none
  -- output parameters become fresh holes
  let mut args' := #[]
  for a in args, out in info.outParams ++ List.replicate args.size false do
    if out then args' := args'.push (← evalIn ctx (← freshMeta ctx "an output parameter"))
    else args' := args'.push a
  let g ← getGlobals
  let goalTy := args'.foldl (vApp g) (eval g [] (.const info.name us))
  let goal ← freshMeta ctx "an instance"
  let key ← goalKey ctx goalTy
  let saved ← get
  let mut ss : SynthState R := { table := ({} : Std.HashMap String (Entry R)).insert key { waiters := #[.root] } }
  ss := { ss with gens := #[← mkGenerator ctx key goal goalTy] }
  while ss.result.isNone do
    ss := { ss with steps := ss.steps + 1 }
    if ss.steps > 4000 then
      set saved
      throwAt ctx.info s!"instance problem is too big: {← showType ctx ty}"
    if let some (c, a) := ss.resume.back? then
      ss := { ss with resume := ss.resume.pop }
      set c.state
      match c.subgoals with
      | (h, hty) :: rest =>
        let ok ← try
            unify ctx.lvl hty (← evalIn ctx a.ty)
            unify ctx.lvl (← evalIn ctx h) (← evalIn ctx a.val)
            pure true
          catch _ => pure false
        if ok then ss ← consume ctx ss { c with subgoals := rest, state := ← get }
      | [] => pure ()
    else if let some gen := ss.gens.back? then
      if h : gen.next < gen.candidates.size then
        let (e, ety) := gen.candidates[gen.next]
        ss := { ss with gens := ss.gens.set! (ss.gens.size - 1) { gen with next := gen.next + 1 } }
        set gen.state
        let applied ← try some <$> applyInstance ctx gen.goal gen.goalTy e ety catch _ => pure none
        if let some subgoals := applied then
          ss ← consume ctx ss { key := gen.key, goal := gen.goal, goalTy := gen.goalTy, subgoals, state := ← get }
      else
        ss := { ss with gens := ss.gens.pop }
    else break
  set saved
  match ss.result with
  | none => return none
  | some a =>
    -- the answer also determines the output parameters
    unify ctx.lvl ty (← evalIn ctx a.ty)
    return some a.val
where
  /-- A consumer with no subgoals left is an answer for its goal; otherwise it waits for
  the answers to its first subgoal (making a generator if the subgoal is new). -/
  consume (ctx : LocalCtx R) (ss : SynthState R) (c : Consumer R) : ElabM R (SynthState R) := do
    set c.state
    match c.subgoals with
    | [] =>
      let val ← zonk ctx.lvl c.goal
      let ty ← zonk ctx.lvl (quote (← getGlobals) ctx.lvl c.goalTy)
      unless val.mvars.isEmpty && ty.mvars.isEmpty do return ss
      let entry := ss.table.getD c.key {}
      if entry.answers.any (fun a => a.val == val && a.ty == ty) then return ss
      let a : Answer R := { val, ty }
      let mut ss := { ss with table := ss.table.insert c.key { entry with answers := entry.answers.push a } }
      for w in entry.waiters do
        match w with
        | .root => ss := { ss with result := some a }
        | .consumer c' => ss := { ss with resume := ss.resume.push (c', a) }
      return ss
    | (h, hty) :: _ =>
      let key ← goalKey ctx hty
      match ss.table.get? key with
      | some entry =>
        let mut ss := { ss with table := ss.table.insert key { entry with waiters := entry.waiters.push (.consumer c) } }
        for a in entry.answers do ss := { ss with resume := ss.resume.push (c, a) }
        return ss
      | none =>
        let gen ← mkGenerator ctx key h hty
        return { ss with table := ss.table.insert key { waiters := #[.consumer c] }, gens := ss.gens.push gen }

/-- Can the problem be attempted? Its non-output arguments must have no unsolved holes. -/
def instReady (ctx : LocalCtx R) (ty : VTy R) : ElabM R Bool := do
  let some (info, _, args) ← classOf? ty | return false
  let g ← getGlobals
  for a in args, out in info.outParams ++ List.replicate args.size false do
    unless out do
      let t ← zonk ctx.lvl (quote g ctx.lvl a)
      unless t.mvars.isEmpty do return false
  return true

/-- Try the pending instance problems; `force` also tries those that aren't ready.
Returns whether any was solved. Fails if a problem has no instance. -/
def synthPending (force : Bool := false) : ElabM R Bool := do
  let pending := (← get).pendingInsts
  modify fun s => { s with pendingInsts := #[] }
  let mut progress := false
  let mut left := #[]
  for (ctx, m, ty) in pending do
    if (← zonk ctx.lvl m).mvars.isEmpty then progress := true; continue
    if !(← instReady ctx ty) && !force then left := left.push (ctx, m, ty); continue
    match ← synthInstance ctx ty with
    | some t =>
      unify ctx.lvl (← evalIn ctx m) (← evalIn ctx t)
      -- (11q) which instance, for the infoview (at the application that needed it)
      if ctx.info.stop > 0 then pushInfo (.inst ctx.info ctx ty t)
      progress := true
    | none =>
      if ← instReady ctx ty then
        throwAt ctx.info s!"failed to synthesize an instance of {← showType ctx ty}"
      left := left.push (ctx, m, ty)
  modify fun s => { s with pendingInsts := left ++ s.pendingInsts }
  pure progress

/-- Record an instance problem, and try it right away. -/
def addInstProblem (ctx : LocalCtx R) (m : Term R) (ty : VTy R) : ElabM R Unit := do
  modify fun s => { s with pendingInsts := s.pendingInsts.push (ctx, m, ty) }
  if let .mvar k := m.spine.1 then
    modify fun s => { s with metas := s.metas.modify k ({ · with isInst := true }) }
  let _ ← synthPending

/-- At the end of a command: solve what can be solved, then report what is stuck. -/
partial def finishInstances : ElabM R Unit := do
  while ← synthPending do pure ()
  let _ ← synthPending (force := true)
  while ← synthPending do pure ()
  if let some (ctx, _, ty) := (← get).pendingInsts[0]? then
    throwAt ctx.info s!"type class problem is stuck (holes in its arguments): {← showType ctx ty}"

end Wiz.Elab
