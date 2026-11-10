import Wiz.Compiler.DropSpec

/-!
# Borrowed parameters (stage 8e)

A parameter is **borrowed** when the function never consumes it (Lean 4's borrow
inference, `Lean.Compiler.IR.Borrow`, Ullrich & de Moura, *Counting Immutable Beans*,
IFL 2019): the caller keeps its reference and lends it for the call, so a function that
only looks at its argument (the length of a list, a lookup in a tree) neither
increments nor decrements it, and the fields it reads from it are borrowed too.

A parameter is **owned** if it is

* consumed: returned, stored in a constructor, captured by a closure (`pap`), applied or
  passed to a closure (`ap`), passed to a native operation, or passed to an owned
  parameter of a function or join point;
* reused (`reset`): its cell, or the cell of a field read from it, is reused for a new
  object when everything is owned (`Reuse.lean`). Borrowing it would lose the in-place
  update;
* passed, in owned form, to a borrowed parameter of a **tail call** within its own
  recursive group: the caller would have to drop it after the call, which then is no
  longer a tail call (Lean's rule: the callee's parameter becomes owned instead, so loops
  stay loops). Likewise a join point parameter that receives an owned value is owned
  (a jump can't be followed by a drop).

Everything else starts borrowed, and the rules above are applied until nothing changes
(a greatest fixed point over the whole program, like the self-hosted backend's
`sigsFix`). Then `RC.lean` lends the arguments in borrowed positions.

**Closures** call functions with owned arguments (the runtime knows nothing of
borrowing): a partially applied function with borrowed parameters gets a wrapper
`f._owned` with all parameters owned, which calls `f` and drops the borrowed ones after.
-/

namespace Wiz.IR

/-- A parameter: of the function, or of one of its join points. -/
inductive PRef where
  | fn (i : Nat)
  | jp (j : JoinId) (i : Nat)

/-- The current guess: which parameters are borrowed (`true`). -/
structure BState where
  fns : Std.HashMap Name (Array Bool) := {}
  jps : Std.HashMap Name (Std.HashMap JoinId (Array Bool)) := {}
  changed : Bool := false

abbrev BM := StateM BState

def ownFn (g : Name) (i : Nat) : BM Unit := modify fun s =>
  match s.fns.get? g with
  | some bs => if bs[i]?.getD false then { s with fns := s.fns.insert g (bs.set! i false), changed := true } else s
  | none => s

def ownJp (f : Name) (j : JoinId) (i : Nat) : BM Unit := modify fun s =>
  match (s.jps.get? f).bind (·.get? j) with
  | some bs =>
    if bs[i]?.getD false then
      { s with jps := s.jps.insert f ((s.jps.getD f {}).insert j (bs.set! i false)), changed := true }
    else s
  | none => s

/-- One pass over the body of `f`: make owned what the body consumes. `bor` are the
variables known to be borrowed (borrowed parameters and their fields), `pref` the
parameters. `sameGroup g` says `g` is in `f`'s recursive group. -/
partial def collectBorrow (f : Name) (sameGroup : Name → Bool) (bor : Std.HashMap Var Bool)
    (pref : Std.HashMap Var PRef) : Body → BM Unit
  | .vdecl x e rest => do
    let s ← get
    match e with
    | .proj _ y =>
      collectBorrow f sameGroup (bor.insert x (bor.getD y false)) pref rest
    | .fap g as =>
      let sig := s.fns.get? g
      let borrowedAt (i : Nat) : Bool := (sig.bind (·[i]?)).getD false
      for (a, i) in as.zipIdx do
        if !borrowedAt i then consume a
      -- a tail call in the group: an owned argument makes the parameter owned
      if let .ret r := rest then
        if r == x && sameGroup g then
          for (a, i) in as.zipIdx do
            if borrowedAt i && !bor.getD a false then ownFn g i
      collectBorrow f sameGroup bor pref rest
    | e =>
      e.args.forM consume
      collectBorrow f sameGroup bor pref rest
  | .case _ alts => alts.forM (collectBorrow f sameGroup bor pref)
  | .ret x => consume x
  | .jdecl j ps body k => do
    let sig := ((← get).jps.get? f).bind (·.get? j)
    let (bor', pref') := ps.zipIdx.foldl (fun (b, p) (x, i) =>
      (b.insert x ((sig.bind (·[i]?)).getD false), p.insert x (.jp j i))) (bor, pref)
    collectBorrow f sameGroup bor' pref' body
    collectBorrow f sameGroup bor pref k
  | .jmp j as => do
    let sig := ((← get).jps.get? f).bind (·.get? j)
    for (a, i) in as.zipIdx do
      if (sig.bind (·[i]?)).getD false then
        -- an owned value can't be lent to a jump (nothing runs after it to drop it)
        if !bor.getD a false then ownJp f j i
      else consume a
  | .dup _ b | .drop _ b => collectBorrow f sameGroup bor pref b
  | .unreachable => pure ()
where
  consume (y : Var) : BM Unit :=
    match pref.get? y with
    | some (.fn i) => ownFn f i
    | some (.jp j i) => ownJp f j i
    | none => pure ()

/-- The join points of a body and their parameters. -/
partial def joinPoints : Body → Array (JoinId × Array Var) → Array (JoinId × Array Var)
  | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => joinPoints b acc
  | .case _ alts, acc => alts.foldl (fun acc a => joinPoints a acc) acc
  | .jdecl j ps body k, acc => joinPoints k (joinPoints body (acc.push (j, ps)))
  | _, acc => acc

/-- Does the body allocate an object (something a `reset` could be paired with)? -/
partial def allocates : Body → Bool
  | .vdecl _ (.ctor _ as) b => !as.isEmpty || allocates b
  | .vdecl _ _ b | .dup _ b | .drop _ b => allocates b
  | .case _ alts => alts.any allocates
  | .jdecl _ _ body k => allocates body || allocates k
  | _ => false

/-- The variables reset in a body, and the object each projected variable was read from. -/
partial def resetsAndParents : Body → Array Var × Std.HashMap Var Var → Array Var × Std.HashMap Var Var
  | .vdecl x e b, (rs, ps) =>
    let acc := match e with
      | .reset y => (rs.push y, ps)
      | .proj _ y => (rs, ps.insert x y)
      | _ => (rs, ps)
    resetsAndParents b acc
  | .dup _ b, acc | .drop _ b, acc => resetsAndParents b acc
  | .case _ alts, acc => alts.foldl (fun acc a => resetsAndParents a acc) acc
  | .jdecl _ _ body k, acc => resetsAndParents k (resetsAndParents body acc)
  | _, acc => acc

/-- The variables whose cells (or whose fields' cells) are reused when everything is
owned: parameters among them must stay owned. -/
def reusedVars (d : Decl) : Std.HashSet Var := Id.run do
  if !allocates d.body then return {}
  let (rs, parents) := resetsAndParents d.optimize.body (#[], {})
  let mut out : Std.HashSet Var := {}
  for r in rs do
    let mut y := r
    let mut fuel := parents.size + 1
    out := out.insert y
    while fuel > 0 do
      fuel := fuel - 1
      match parents.get? y with
      | some p => out := out.insert p; y := p
      | none => break
  return out

/-! ### Recursive groups (Tarjan's strongly connected components) -/

structure SccState where
  index : Std.HashMap Name Nat := {}
  low : Std.HashMap Name Nat := {}
  onStack : Std.HashSet Name := {}
  stack : Array Name := #[]
  counter : Nat := 0
  comp : Std.HashMap Name Nat := {}
  ncomp : Nat := 0

partial def sccVisit (g : Std.HashMap Name (Array Name)) (v : Name) : StateM SccState Unit := do
  modify fun s => { s with index := s.index.insert v s.counter, low := s.low.insert v s.counter,
                           counter := s.counter + 1, stack := s.stack.push v, onStack := s.onStack.insert v }
  for w in g.getD v #[] do
    if !g.contains w then continue
    if !(← get).index.contains w then
      sccVisit g w
      modify fun s => { s with low := s.low.insert v (min (s.low.getD v 0) (s.low.getD w 0)) }
    else if (← get).onStack.contains w then
      modify fun s => { s with low := s.low.insert v (min (s.low.getD v 0) (s.index.getD w 0)) }
  let s ← get
  if s.low.getD v 0 == s.index.getD v 0 then
    let mut stack := s.stack
    let mut onStack := s.onStack
    let mut comp := s.comp
    while !stack.isEmpty do
      let w := stack.back!
      stack := stack.pop
      onStack := onStack.erase w
      comp := comp.insert w s.ncomp
      if w == v then break
    set { s with stack, onStack, comp, ncomp := s.ncomp + 1 }

/-- The functions a body calls directly. -/
partial def callees : Body → Array Name → Array Name
  | .vdecl _ (.fap g _) b, acc => callees b (acc.push g)
  | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => callees b acc
  | .case _ alts, acc => alts.foldl (fun acc a => callees a acc) acc
  | .jdecl _ _ body k, acc => callees k (callees body acc)
  | _, acc => acc

/-- The recursive group of each function. -/
def recursiveGroups (decls : Array Decl) : Std.HashMap Name Nat :=
  let g : Std.HashMap Name (Array Name) := decls.foldl (fun m d => m.insert d.name (callees d.body #[])) {}
  let run : StateM SccState Unit := decls.forM fun d => do
    unless (← get).index.contains d.name do sccVisit g d.name
  (run.run {}).2.comp

/-! ### Inference -/

/-- The borrowed parameters of every function and join point of a program. -/
def inferBorrow (decls : Array Decl) : BState := Id.run do
  let groups := recursiveGroups decls
  -- everything borrowed, except what is reused
  let mut st : BState := {}
  for d in decls do
    let reused := reusedVars d
    st := { st with fns := st.fns.insert d.name (d.params.map (!reused.contains ·)) }
    let jps := (joinPoints d.body #[]).foldl (fun m (j, ps) => m.insert j (ps.map (!reused.contains ·))) {}
    st := { st with jps := st.jps.insert d.name jps }
  let mut fuel := decls.size * 4 + 100
  while fuel > 0 do
    fuel := fuel - 1
    let round : BM Unit := decls.forM fun d => do
      let sig := ((← get).fns.get? d.name).getD #[]
      let (bor, pref) := d.params.zipIdx.foldl (fun (b, p) (x, i) =>
        (b.insert x (sig[i]?.getD false), p.insert x (PRef.fn i)))
        (({} : Std.HashMap Var Bool), ({} : Std.HashMap Var PRef))
      let grp := groups.get? d.name
      collectBorrow d.name (fun g => grp.isSome && groups.get? g == grp) bor pref d.body
    let ((), st') := round.run { st with changed := false }
    st := st'
    if !st.changed then break
  return st

/-! ### Closures -/

def ownedWrapper (f : Name) : Name := f ++ "._owned"

/-- The functions partially applied in a body. -/
partial def papped : Body → Std.HashSet Name → Std.HashSet Name
  | .vdecl _ (.pap g _) b, acc => papped b (acc.insert g)
  | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => papped b acc
  | .case _ alts, acc => alts.foldl (fun acc a => papped a acc) acc
  | .jdecl _ _ body k, acc => papped k (papped body acc)
  | _, acc => acc

/-- Partial applications of the functions in `w` go to their wrappers. -/
partial def toWrappers (w : Std.HashSet Name) : Body → Body
  | .vdecl x (.pap g as) b => .vdecl x (.pap (if w.contains g then ownedWrapper g else g) as) (toWrappers w b)
  | .vdecl x e b => .vdecl x e (toWrappers w b)
  | .dup x b => .dup x (toWrappers w b)
  | .drop x b => .drop x (toWrappers w b)
  | .case x alts => .case x (alts.map (toWrappers w))
  | .jdecl j ps body k => .jdecl j ps (toWrappers w body) (toWrappers w k)
  | b => b

/-- The backend's optimisations for a whole program: borrowed parameters (inferred over
all functions), then `Decl.optimize` for each function, then drop specialisation. -/
def optimizeProgram (decls : Array Decl) : Array Decl :=
  let decls := decls.map fun d => { d with body := (elimDead d.body).1 }
  let st := inferBorrow decls
  let borrows (d : Decl) : Bool := ((st.fns.get? d.name).getD #[]).any id
  let pappedFns := decls.foldl (fun acc d => papped d.body acc) {}
  let wrap : Std.HashSet Name := decls.foldl (fun acc d =>
    if borrows d && pappedFns.contains d.name then acc.insert d.name else acc) {}
  let wrappers : Array Decl := decls.filterMap fun d =>
    if wrap.contains d.name then
      let n := d.params.size
      let ps := (List.range n).toArray
      some { name := ownedWrapper d.name, params := ps, body := .vdecl n (.fap d.name ps) (.ret n) }
    else none
  let decls := if wrap.isEmpty then decls else decls.map fun d => { d with body := toWrappers wrap d.body }
  (decls ++ wrappers).map fun d =>
    (d.optimize { fns := st.fns, jps := (st.jps.get? d.name).getD {} }).specializeDrops

end Wiz.IR
