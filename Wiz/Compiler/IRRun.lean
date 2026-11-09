import Wiz.Compiler.Reuse
import Wiz.Compiler.Run

/-!
# Running the IR, with a checked heap

An interpreter for the IR that keeps an explicit heap of reference-counted objects, so
the output of `RC.lean` can be tested: using a freed object, freeing twice, or ending
with objects still allocated (a leak) are errors. `#run e` compiles `e` through the
whole backend pipeline and runs it here.

Numbers are scalars here (the C runtime adds big numbers). As in the interpreter, a
number looks like its unary payload when projected (`natView`); the objects that
creates are fresh references.
-/

namespace Wiz.IR

inductive IVal where
  | num (n : Nat)
  | tag (t : Nat)
  | erased
  | ptr (id : Nat)
  deriving Inhabited, BEq, Repr

inductive Obj where
  | ctor (tag : Nat) (fields : Array IVal)
  | clo (f : Name) (args : Array IVal)
  /-- a cell kept by `reset` for `reuse` -/
  | token (size : Nat)
  deriving Inhabited

structure Heap where
  objs : Std.HashMap Nat (Nat × Obj) := {}
  next : Nat := 0
  allocs : Nat := 0
  /-- steps left, so that a divergent program stops -/
  fuel : Nat := 10000000

abbrev RunM := StateT Heap (Except String)

def alloc (o : Obj) : RunM IVal := do
  let h ← get
  set { h with objs := h.objs.insert h.next (1, o), next := h.next + 1, allocs := h.allocs + 1 }
  pure (.ptr h.next)

def getObj (id : Nat) : RunM (Nat × Obj) := do
  match (← get).objs.get? id with
  | some o => pure o
  | none => throw s!"use of a freed object (#{id})"

def dupV : IVal → RunM Unit
  | .ptr id => do
    let (rc, o) ← getObj id
    modify fun h => { h with objs := h.objs.insert id (rc + 1, o) }
  | _ => pure ()

partial def dropV : IVal → RunM Unit
  | .ptr id => do
    let (rc, o) ← getObj id
    if rc > 1 then modify fun h => { h with objs := h.objs.insert id (rc - 1, o) }
    else
      modify fun h => { h with objs := h.objs.erase id }
      match o with
      | .ctor _ fs => fs.forM dropV
      | .clo _ as => as.forM dropV
      | .token _ => pure ()
  | _ => pure ()

/-- The `natView` of a number, as fresh objects. -/
def natField (n : Nat) (i : Nat) : RunM IVal := do
  if i == 0 then return .tag (if n == 0 then 0 else 1)
  let unitPair ← alloc (.ctor 0 #[.erased, .erased])
  if n == 0 then return unitPair
  alloc (.ctor 0 #[.num (n - 1), unitPair])

def nativeOp (op : Name) (args : Array IVal) : RunM IVal := do
  let n (i : Nat) : Nat := match args[i]? with
    | some (.num k) => k
    | some (.tag k) => k
    | _ => 0
  match op with
  | "nat.succ" => pure (.num (n 0 + 1))
  | "nat.pred" => pure (.num (n 0 - 1))
  | "nat.add" => pure (.num (n 0 + n 1))
  | "nat.sub" => pure (.num (n 0 - n 1))
  | "nat.mul" => pure (.num (n 0 * n 1))
  | "nat.beq" => pure (.tag (if n 0 == n 1 then 1 else 0))
  | "nat.blt" => pure (.tag (if n 0 < n 1 then 1 else 0))
  -- the interpreter doesn't memoise: a suspension is its function
  | "memo" => pure (args[1]?.getD (.tag 0))
  | "natTag" => pure (.tag (if n 0 == 0 then 0 else 1))
  | "tag" =>
    let t ← match (args[0]? : Option IVal) with
      | some (.ptr id) => do
        match (← getObj id).2 with
        | .ctor t _ => pure t
        | _ => throw "tag of a closure or token"
      | some (.tag t) => pure t
      | some (.num k) => pure (if k == 0 then 0 else 1)
      | _ => pure 0
    args.forM dropV
    pure (.tag t)
  | "fieldAt" =>
    match (args[0]? : Option IVal), (args[1]? : Option IVal) with
    | some (.ptr id), some (.num i) => do
      let .ctor _ fs := (← getObj id).2 | throw "fieldAt of a closure or token"
      let fv := fs[i]?.getD .erased
      dupV fv
      dropV (.ptr id)
      pure fv
    | some (.num k), some (.num 0) => pure (.num (k - 1))
    | _, _ => throw "fieldAt: bad arguments"
  | "mkObj" =>
    let t := match (args[0]? : Option IVal) with
      | some (.tag t) => t
      | some (.num t) => t
      | _ => 0
    -- the fields: nested pairs ending in ◾
    let mut fs : Array IVal := #[]
    let mut l := (args[1]?).getD .erased
    let mut fuel := 100000
    while fuel > 0 do
      fuel := fuel - 1
      match l with
      | .ptr id =>
        let .ctor _ #[a, rest] := (← getObj id).2 | throw "mkObj: not a list"
        dupV a; dupV rest
        dropV l
        fs := fs.push a
        l := rest
      | _ => break
    if fs.isEmpty then pure (.tag t) else alloc (.ctor t fs)
  | "lazyTag" =>
    let t ← match (args[0]? : Option IVal) with
      | some (.ptr id) => do
        match (← getObj id).2 with
        | .ctor 1000 _ => pure 1
        | .ctor 1001 _ => pure 2
        | .ctor 1002 _ => pure 3
        | _ => pure 0
      | _ => pure 0
    args.forM dropV
    pure (.tag t)
  | "lazySet" =>
    -- as in the C runtime: a shared lazy cell becomes ⟨1002 p⟩ (memoised `out`)
    let x := (args[0]?).getD .erased
    let pv := (args[1]?).getD .erased
    match x with
    | .ptr id => do
      match ← getObj id with
      | (rc, .ctor t fs) =>
        if rc > 1 && (t == 1000 || t == 1001) then
          modify fun h => { h with objs := h.objs.insert id (rc - 1, .ctor 1002 #[pv]) }
          fs.forM dropV
          dupV pv
        else dropV x
      | _ => dropV x
    | _ => pure ()
    pure pv
  | _ => throw s!"{op}: foreign functions only run in compiled code (wiz run)"

mutual

/-- Call a top-level function; the arguments are owned by the callee. -/
partial def call (prog : Std.HashMap Name Decl) (f : Name) (args : Array IVal) : RunM IVal := do
  let some d := prog.get? f | throw s!"no function {f}"
  unless d.params.size == args.size do throw s!"{f} expects {d.params.size} arguments, got {args.size}"
  let env := (d.params.zip args).foldl (fun m (x, v) => m.insert x v) {}
  run prog env {} d.body

partial def apply (prog : Std.HashMap Name Decl) (f : IVal) (args : Array IVal) : RunM IVal := do
  let .ptr id := f | throw "applying a non-closure"
  let (rc, o) ← getObj id
  let .clo g captured := o | throw "applying a non-closure"
  -- take the captured arguments: move them out of a unique closure, else share them
  if rc == 1 then modify fun h => { h with objs := h.objs.erase id }
  else
    captured.forM dupV
    dropV f
  let all := captured ++ args
  let arity := ((prog.get? g).map (·.params.size)).getD 0
  if all.size == arity then call prog g all
  else if all.size < arity then alloc (.clo g all)
  else
    let r ← call prog g (all.extract 0 arity)
    apply prog r (all.extract arity all.size)

partial def run (prog : Std.HashMap Name Decl) (env : Std.HashMap Var IVal)
    (joins : Std.HashMap JoinId (Array Var × Body)) (b : Body) : RunM IVal := do
  modify fun h => { h with fuel := h.fuel - 1 }
  if (← get).fuel == 0 then throw "out of fuel"
  let get (x : Var) : RunM IVal := match env.get? x with
    | some v => pure v
    | none => throw s!"unbound x{x}"
  match b with
  | .vdecl x e rest =>
    let v ← match e with
      | .erased => pure .erased
      | .lit n => pure (.num n)
      | .ctor t as =>
        if as.isEmpty then pure (.tag t) else alloc (.ctor t (← as.mapM get))
      | .proj i y => do
        match ← get y with
        | .ptr id => do
          let .ctor _ fs := (← getObj id).2 | throw "projection from a closure or token"
          let fv := fs[i]?.getD .erased
          dupV fv
          pure fv
        | .num n => natField n i
        | .tag 0 => natField 0 i
        | v => throw s!"projection from a scalar {repr v}"
      | .fap f as => call prog f (← as.mapM get)
      | .pap f as => alloc (.clo f (← as.mapM get))
      | .ap f as => apply prog (← get f) (← as.mapM get)
      | .prim op as => nativeOp op (← as.mapM get)
      | .reset y => do
        let v ← get y
        match v with
        | .ptr id =>
          match ← getObj id with
          | (1, .ctor _ fs) => do
            fs.forM dropV
            modify fun h => { h with objs := h.objs.insert id (1, .token fs.size) }
            pure v
          | _ => dropV v; pure .erased
        | _ => pure .erased
      | .reuse tok t as => do
        let vs ← as.mapM get
        match ← get tok with
        | .ptr id =>
          match ← getObj id with
          | (_, .token n) =>
            if n == vs.size then
              modify fun h => { h with objs := h.objs.insert id (1, .ctor t vs) }
              pure (.ptr id)
            else
              modify fun h => { h with objs := h.objs.erase id }
              alloc (.ctor t vs)
          | _ => throw "reuse of a non-token"
        | _ => alloc (.ctor t vs)
    run prog (env.insert x v) joins rest
  | .case x alts =>
    let t ← match ← get x with
      | .tag t => pure t
      | .num n => pure (if n == 0 then 0 else 1)
      | .ptr id => do
        match (← getObj id).2 with
        | .ctor t _ => pure t
        | _ => throw "case on a closure or token"
      | .erased => throw "case on ◾"
    match alts[t]? with
    | some alt => run prog env joins alt
    | none => throw s!"no branch for tag {t}"
  | .ret x => get x
  | .jdecl j ps body k => run prog env (joins.insert j (ps, body)) k
  | .jmp j as =>
    let some (ps, body) := joins.get? j | throw s!"no join point j{j}"
    let vs ← as.mapM get
    run prog ((ps.zip vs).foldl (fun m (p, v) => m.insert p v) {}) joins body
  | .dup x rest => dupV (← get x); run prog env joins rest
  | .drop x rest => dropV (← get x); run prog env joins rest
  | .unreachable => throw "reached an impossible case"

end

/-- An IR value as an interpreter value, for `readback`. -/
partial def toRVal (h : Heap) : IVal → RVal
  | .num n => .nat n
  | .tag t => .obj t #[]
  | .erased => .erased
  | .ptr id => match h.objs.get? id with
    | some (_, .ctor 1000 _) => .coit .erased .erased .erased .erased
    | some (_, .ctor 1001 _) => .scofix .erased .erased .erased
    | some (_, .ctor 1002 _) => .coit .erased .erased .erased .erased
    | some (_, .ctor t fs) => .obj t (fs.map (toRVal h))
    | some (_, .clo _ _) => .clo [] .erased
    | some (_, .token _) => .erased
    | none => .erased

/-- Run `main`; returns the result (as an interpreter value), the number of objects
allocated, and an error if anything leaked. -/
def runProgram (decls : Array Decl) : Except String (RVal × Nat) := do
  let prog := decls.foldl (fun m d => m.insert d.name d) {}
  let (v, h) ← (call prog "wiz.entry" #[]).run {}
  let r := toRVal h v
  let ((), h) ← (dropV v).run h
  unless h.objs.isEmpty do throw s!"{h.objs.size} objects leaked"
  pure (r, h.allocs)

end Wiz.IR
