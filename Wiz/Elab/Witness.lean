import Wiz.Elab.Class

/-!
# Witnesses for partial definitions

A partial definition `partial def f : T := …` is opaque to the kernel: its body may loop,
so the kernel never unfolds it, and `f : T` is assumed. That is only sound when `T` is
inhabited, so the kernel asks for a **witness**, a term `w : T` that it checks
(`addPartialDecl`). The user can write one (`partial (default := w) def f …`); usually the
elaborator finds one here, by a small search over the shape of `T`:

* a hypothesis (a variable bound by the type's `Π`s) of the right type;
* `fun x => w` for a `Π`, a pair of witnesses for a `Σ`, `tt`, a tag, `Unit` for a sort,
  `∞`, a quantity, `refl` for an equation whose sides unify;
* `Inhabited.default` when an instance resolves (`lib/Deriving.wiz`);
* a constant whose type ends in the type's head (`T.mk`, `List.nil`, `StrMap.empty`),
  applied to holes: unifying its conclusion with the goal fixes the indices (so the
  constructor `T.mk : T .t` is no witness of `T .f`), and the holes left are filled by
  the search again, constructors first, to a bounded depth.

The search only proposes: whatever it finds, the kernel checks.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- The head constant of the conclusion of a declaration's type. -/
private def resultHead : Term R → Option Name
  | .pi _ _ _ _ b _ => resultHead b
  | t => match t.spine.1 with
    | .const n _ => some n
    | _ => none

private def numPis : Term R → Nat
  | .pi _ _ _ _ b _ => numPis b + 1
  | _ => 0

/-- Run `x`; if it fails (or throws), restore the state. -/
private def attempt (x : ElabM R (Option α)) : ElabM R (Option α) := do
  let saved ← get
  try
    match ← x with
    | some a => pure (some a)
    | none => set saved; pure none
  catch _ => set saved; pure none

/-- The names a type is known by: the definitions it unfolds through, then the head of
its shape (an inductive type's name, or an axiom). -/
private partial def headNames (v : Val R) (acc : List Name := []) : ElabM R (List Name) := do
  match ← forceMeta v with
  | .unfold n _ _ v => headNames v.get (acc ++ [n])
  | .lazyInd _ _ _ _ _ _ _ _ _ v => headNames v.get acc
  | .mu _ _ _ _ _ (some (T, _, _)) | .nu _ _ _ _ _ (some (T, _, _)) => pure (acc ++ [T])
  | .neutral (.global T _) _ => pure (acc ++ [T])
  | _ => pure acc

mutual
/-- A term of type `ty` in `ctx`, found within `fuel` nested constant applications. -/
partial def witness (ctx : LocalCtx R) (ty : VTy R) (fuel : Nat) : ElabM R (Option (Term R)) := do
  if fuel == 0 then return none
  let g ← getGlobals
  let names ← headNames ty
  let ty ← force ty
  -- a hypothesis
  for j in [0:ctx.lvl] do
    if ctx.bound[j]! then
      if let some t ← attempt (do unify ctx.lvl ctx.types[j]! ty; pure (some (Term.var j))) then
        return some t
  match ty with
  | .pi x _ _ A B _ =>
    let some b ← witness (ctx.bind x A) (Closure.inst g B (.var ctx.lvl)) fuel | return none
    return some (.lam x b)
  | .sort l => return some (.unit l)
  | .unit _ => return some .tt
  | .qty => return some (.qlit QuantitySyntax.explicitDefault)
  | .size => return some .szInf
  | .enum ls => return if ls.isEmpty then none else some (.tag ls 0)
  | .sigma _ _ A B _ => attempt do
    let some a ← witness ctx A fuel | return none
    let some b ← witness ctx (Closure.inst g B (eval g ctx.env a)) fuel | return none
    return some (.pair a b)
  | .neutral (.eq A a b) #[] => attempt do
    unify ctx.lvl a b
    return some (.refl (quote g ctx.lvl A) (quote g ctx.lvl a))
  | _ =>
    if names.isEmpty then return none
    -- `Inhabited.default`, when an instance resolves
    if g.contains "Inhabited.default" && (← get).classes.any (·.name == "Inhabited") then
      if let some t ← applyConst ctx ty "Inhabited.default" fuel then return some t
    -- constants whose type ends in one of the names: constructors first
    let cands := g.order.filter fun c => match g.find? c with
      | some d => !names.contains c && (resultHead d.type).any names.contains
      | none => false
    let (ctors, others) := cands.partition fun c => (g.find? c).any (·.inline)
    for c in ctors ++ others do
      if let some t ← applyConst ctx ty c (fuel - 1) then return some t
    return none

/-- Apply the constant `c` to holes, unify its conclusion with `ty`, and fill the holes
unification left open: instance arguments by instance resolution, the others by
`witness`. -/
partial def applyConst (ctx : LocalCtx R) (ty : VTy R) (c : Name) (fuel : Nat) :
    ElabM R (Option (Term R)) := attempt do
  let g ← getGlobals
  let some d := g.find? c | return none
  let us ← d.levelParams.mapM fun _ => freshLevelMeta
  let mut t : Term R := .const c us
  let mut cty := eval g [] (d.type.instLevels d.levelParams us)
  let mut holes : Array (Term R × VTy R × BinderInfo) := #[]
  for _ in [0:numPis d.type] do
    match ← forceMeta cty with
    | .pi x bi _ dom cod _ =>
      let m ← freshMeta ctx s!"argument {x}"
      holes := holes.push (m, dom, bi)
      t := .app t m
      cty := Closure.inst g cod (← evalIn ctx m)
    | _ => return none
  unify ctx.lvl ty cty
  for (m, dom, bi) in holes do
    if let .neutral (.mvar _) _ ← forceMeta (← evalIn ctx m) then
      let w ← if bi == .instImplicit then synthInstance ctx dom else witness ctx dom fuel
      let some w := w | return none
      unify ctx.lvl (← evalIn ctx m) (← evalIn ctx w)
  let t ← zonk ctx.lvl t
  if t.mvars.isEmpty then return some t else return none
end

/-- A witness for a closed type, with the universe levels the search left open set to
`0`; `none` if the search finds nothing. -/
def findWitness (ty : Term R) (fuel : Nat := 4) : ElabM R (Option (Term R)) := do
  let some w ← witness {} (← evalIn {} ty) fuel | return none
  modify fun s => { s with levelMetas := s.levelMetas.map fun l => l.orElse fun _ => some .zero }
  let w ← zonk 0 w
  return if w.mvars.isEmpty && !w.hasLevelMVar then some w else none

end Wiz.Elab
