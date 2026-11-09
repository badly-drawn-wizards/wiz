import Wiz.Compiler.Erase

/-!
# Running erased programs

An environment-based interpreter for `ETerm`. Strict (call-by-value), except that
coinductive values (`coit`, `scofix`) are lazy and unfold only under `out`.

The generic eliminators are **primitives that walk the description** at runtime. A
description is an ordinary runtime value: `⟨0 i⟩` (ret), `⟨1 ◾ F⟩` (arg), `⟨2 j D⟩`
(rec), `⟨3 ◾ j D⟩` (hrec), with `⟨4 ◾ F⟩` for an arg that is a tag and `⟨5 D⟩` marking
the description of numbers. A data value is a flat object `⟨tag f₁ … fₙ⟩` (see
`Erase.lean`); `unpack` gives its payload of nested pairs, `⟨0 tag ⟨0 f₁ … ⟩⟩`, and
`pack` goes back.

    ind D m i x      = m i u (hyps D u),   u = unpack D x
                                          hyps (rec j D') ⟨y, r⟩ = ⟨ind D m j y, hyps D' r⟩
                                          hyps (hrec j D') ⟨k, r⟩ = ⟨fun h => ind D m (j h) (k h), hyps D' r⟩
    out (coit D step i s) = map D (coit D step) i (step i s)

`#eval` reads a value back into a term using its **type**, so results print with
constructor names.
-/

namespace Wiz

/-- Partially applied runtime primitives (closures the runtime itself creates). -/
inductive PapOp where
  /-- `fun s => delim mret marg mrec mhrec (F s)`: args `mret marg mrec mhrec F`, arity 1 -/
  | delimRec
  /-- `fun h => ind D m (j h) (k h)`: args `D m j k`, arity 1 -/
  | indK
  /-- `fun h => f (j h) (k h)`: args `f j k`, arity 1 -/
  | mapK
  /-- `fun j s => coit D step j s`: args `D step`, arity 2 -/
  | coitK
  /-- `fun j i a => scofix f i a`: args `f`, arity 3 -/
  | scofixK
  deriving Repr, Inhabited

inductive RVal where
  | erased
  | obj (tag : Nat) (fields : Array RVal)
  | clo (env : List RVal) (body : ETerm)
  /-- `fix x. body` in `env`: unfolds when applied -/
  | fixv (env : List RVal) (body : ETerm)
  /-- a primitive waiting for more arguments -/
  | pap (op : PapOp) (args : Array RVal)
  /-- a natural number of a type registered with `builtin nat` -/
  | nat (n : Nat)
  /-- a native operation waiting for arguments -/
  | native (op : Name) (args : Array RVal)
  /-- lazy coinductive values -/
  | coit (D step i s : RVal)
  | scofix (f i a : RVal)
  deriving Inhabited

namespace RVal

def arity : PapOp → Nat
  | .delimRec => 6
  | .indK => 5
  | .mapK => 4
  | .coitK => 4
  | .scofixK => 4

/-- A native number looks like its payload when inspected:
`0 ↦ ⟨0 ⟨0⟩ ⟨0 ◾ ◾⟩⟩` and `n+1 ↦ ⟨0 ⟨1⟩ ⟨0 n ⟨0 ◾ ◾⟩⟩⟩`. -/
def natView : Nat → RVal
  | 0 => .obj 0 #[.obj 0 #[], .obj 0 #[.erased, .erased]]
  | n + 1 => .obj 0 #[.obj 1 #[], .obj 0 #[.nat n, .obj 0 #[.erased, .erased]]]

def field (v : RVal) (i : Nat) : RVal :=
  match v with
  | .obj _ fs => fs[i]?.getD .erased
  | .nat n => match natView n with
    | .obj _ fs => fs[i]?.getD .erased
    | _ => .erased
  | _ => .erased

/-- The number a value denotes, if it is one (native, or a unary payload). -/
partial def toNat? : RVal → Option Nat
  | .nat n => some n
  | .obj 0 #[] => some 0
  | .obj 1 #[k] => (toNat? k).map (· + 1)
  | _ => none

/-- The tag of an object (a number's is `0` or `1`). -/
def tagOf : RVal → Nat
  | .obj t _ => t
  | .nat n => if n == 0 then 0 else 1
  | _ => 0

/-- The payload of a flat value, along the description `D` (see `Erase.lean`). -/
partial def unpackWith (apply : RVal → RVal → RVal) (D v : RVal) : RVal :=
  match D with
  | .obj 5 _ => match v with
    | .nat n => natView n
    | .obj 0 _ => natView 0
    | _ => match v.field 0 with
      | .nat n => natView (n + 1)
      | _ => .erased
  | .obj 4 #[_, F] =>
    let t := RVal.obj (tagOf v) #[]
    .obj 0 #[t, rest (apply F t) 0]
  | d => rest d 0
where
  rest (d : RVal) (n : Nat) : RVal :=
    match d with
    | .obj 1 #[_, F] | .obj 4 #[_, F] => let f := v.field n; .obj 0 #[f, rest (apply F f) (n + 1)]
    | .obj 2 #[_, D'] | .obj 3 #[_, _, D'] => .obj 0 #[v.field n, rest D' (n + 1)]
    | _ => .obj 0 #[.erased, .erased]

/-- A payload as a flat value. -/
partial def packWith (apply : RVal → RVal → RVal) (D x : RVal) : RVal :=
  match D with
  | .obj 5 _ => match tagOf (x.field 0) with
    | 0 => .nat 0
    | _ => match (x.field 1).field 0 |>.toNat? with
      | some n => .nat (n + 1)
      | none => .erased
  | .obj 4 #[_, F] => .obj (tagOf (x.field 0)) (fields (apply F (x.field 0)) (x.field 1) #[])
  | d => .obj 0 (fields d x #[])
where
  fields (d x : RVal) (acc : Array RVal) : Array RVal :=
    match d with
    | .obj 1 #[_, F] | .obj 4 #[_, F] => fields (apply F (x.field 0)) (x.field 1) (acc.push (x.field 0))
    | .obj 2 #[_, D'] | .obj 3 #[_, _, D'] => fields D' (x.field 1) (acc.push (x.field 0))
    | _ => acc

/-- A foreign function's key: `extern:cname:kinds:result:io:header:finalizer` (see
`extern`). Kinds: `n` Nat, `u` UInt64, `f` Float64, `s` String, `b` Bool, `v` Unit,
`p` a foreign pointer (the finalizer is for a pointer result), `w` a Wiz value passed as is. -/
structure ExternSig where
  cname : String
  params : List Char
  result : Char
  io : Bool
  header : String
  fin : String := ""

def ExternSig.ofKey? (key : Name) : Option ExternSig :=
  match key.splitOn ":" with
  | ["extern", c, ps, r, io, h, fin] =>
    some { cname := c, params := ps.toList, result := (r.toList.headD 'v'), io := io == "io", header := h, fin }
  | _ => none

def nativeArity (key : Name) : Nat :=
  match ExternSig.ofKey? key with
  | some sig => sig.params.length + (if sig.io then 1 else 0)
  | none => match key with
    | "nat.zero" => 0
    | "nat.succ" | "nat.pred" => 1
    | _ => 2

end RVal

/-- Erased global definitions, by name. -/
abbrev Code := Std.HashMap Name ETerm

mutual

/-- **Exercise 5.2.** Evaluate an erased term. `proj` of `◾` is `◾` (it was a proof or
a type); `case` branches on the tag of an object; `fix` builds a `fixv`; primitives
go to `runPrim`. -/
partial def run (code : Code) (env : List RVal) : ETerm → RVal
  --<sol
  | .erased => .erased
  | .var i => env[i]?.getD .erased
  | .global n => match code[n]? with
    | some (.prim .unreachable #[.global op]) =>
      -- a definition registered as a native operation (`builtin`)
      if RVal.nativeArity op == 0 then .nat 0 else .native op #[]
    | some t => run code [] t
    | none => panic! s!"no code for {n}"
  | .lam _ b => .clo env b
  | .app f a => apply code (run code env f) (run code env a)
  | .letE _ v b => run code (run code env v :: env) b
  | .obj t fs => .obj t (fs.map (run code env))
  | .proj i t => (run code env t).field i
  | .case s bs => match run code env s with
    | .obj t _ => run code env (bs[t]?.getD (.prim .unreachable #[]))
    | _ => panic! "case on a non-object"
  | .fix _ b => .fixv env b
  | .prim op as => runPrim code op (as.map (run code env))
  | .natLit n => .nat n
  --|ex
  --| | .natLit n => .nat n  -- (given)
  --| | t => sorry
  --sol>

partial def apply (code : Code) (f a : RVal) : RVal :=
  match f with
  | .clo env b => run code (a :: env) b
  | .fixv env b => apply code (run code (.fixv env b :: env) b) a
  | .pap op args =>
    let args := args.push a
    if args.size < RVal.arity op then .pap op args else firePap code op args
  | .native op args =>
    let args := args.push a
    if args.size < RVal.nativeArity op then .native op args else fireNative op args
  | _ => .erased

/-- Native arithmetic. `nat.beq` returns a tag of the prelude's `Bool` (`false`, `true`). -/
partial def fireNative (op : Name) (args : Array RVal) : RVal :=
  let n (i : Nat) : Nat := ((args[i]?.getD .erased).toNat?).getD 0
  match op with
  | "nat.succ" => .nat (n 0 + 1)
  | "nat.pred" => .nat (n 0 - 1)
  | "nat.add" => .nat (n 0 + n 1)
  | "nat.sub" => .nat (n 0 - n 1)
  | "nat.mul" => .nat (n 0 * n 1)
  | "nat.beq" => .obj (if n 0 == n 1 then 1 else 0) #[]
  | "nat.blt" => .obj (if n 0 < n 1 then 1 else 0) #[]
  -- the interpreter doesn't memoise: a suspension is its function
  | "memo" => args[1]?.getD .erased
  -- a few pure foreign functions the interpreter knows itself
  | "extern:wiz_nat_show:n:s:pure::" =>
    let chars := (toString (n 0)).toList.foldr (fun c t => RVal.obj 1 #[.obj 0 #[.nat c.toNat], t]) (.obj 0 #[])
    .obj 0 #[chars]
  | _ => panic! s!"{op}: foreign functions only run in compiled code (wiz run)"

partial def applyN (code : Code) (f : RVal) (as : List RVal) : RVal := as.foldl (apply code) f

partial def firePap (code : Code) : PapOp → Array RVal → RVal
  | .delimRec, #[mret, marg, mrec, mhrec, F, s] => delim code mret marg mrec mhrec (apply code F s)
  | .indK, #[D, m, j, k, h] => ind code D m (apply code j h) (apply code k h)
  | .mapK, #[f, j, k, h] => applyN code f [apply code j h, apply code k h]
  | .coitK, #[D, step, j, s] => .coit D step j s
  | .scofixK, #[f, _, i, a] => .scofix f i a
  | _, _ => panic! "bad partial application"

/-- **Exercise 5.3a.** `ind D m i x = m i u (hyps D u)` with the payload `u = unpack D x`,
where `hyps` walks the description alongside the payload, recursing at each `rec`
field (see the module docstring). `D` may be marked as the description of numbers,
`⟨5 D'⟩`: `unpack` needs the mark, `hyps` walks `D'`, and the recursive calls get `D`. -/
partial def ind (code : Code) (D m i x : RVal) : RVal :=
  --<sol
  let u := RVal.unpackWith (apply code) D x
  let d := match D with
    | .obj 5 #[D'] => D'
    | D => D
  applyN code m [i, u, hyps d u]
where
  hyps (d xs : RVal) : RVal :=
    match d with
    | .obj 0 _ => .erased
    | .obj 1 #[_, F] | .obj 4 #[_, F] => hyps (apply code F (xs.field 0)) (xs.field 1)
    | .obj 2 #[j, D'] => .obj 0 #[ind code D m j (xs.field 0), hyps D' (xs.field 1)]
    | .obj 3 #[_, j, D'] => .obj 0 #[.pap .indK #[D, m, j, xs.field 0], hyps D' (xs.field 1)]
    | _ => panic! "ind: not a description"
  --|ex
  --| sorry
  --sol>

partial def delim (code : Code) (mret marg mrec mhrec D : RVal) : RVal :=
  match D with
  | .obj 0 #[i] => apply code mret i
  | .obj 1 #[_, F] | .obj 4 #[_, F] => applyN code marg [.erased, .erased, F, .pap .delimRec #[mret, marg, mrec, mhrec, F]]
  | .obj 2 #[j, D'] => applyN code mrec [.erased, j, D', delim code mret marg mrec mhrec D']
  | .obj 3 #[_, j, D'] => applyN code mhrec [.erased, .erased, j, D', delim code mret marg mrec mhrec D']
  | _ => panic! "Desc.elim: not a description"

/-- **Exercise 5.3b.** Observe a coinductive value. A `coit` runs one step and re-wraps
the recursive positions (`map`); an `scofix` unfolds once; anything else (a `cocon`,
whose erased form is its payload) is already observed. -/
partial def out (code : Code) (x : RVal) : RVal :=
  --<sol
  match x with
  | .coit D step i s => map D (.pap .coitK #[D, step]) (applyN code step [i, s])
  | .scofix f i a => out code (applyN code f [.erased, .pap .scofixK #[f], i, a])
  | v => v
where
  map (d f xs : RVal) : RVal :=
    match d with
    | .obj 0 _ => xs
    | .obj 1 #[_, F] | .obj 4 #[_, F] => .obj 0 #[xs.field 0, map (apply code F (xs.field 0)) f (xs.field 1)]
    | .obj 2 #[j, D'] => .obj 0 #[applyN code f [j, xs.field 0], map D' f (xs.field 1)]
    | .obj 3 #[_, j, D'] => .obj 0 #[.pap .mapK #[f, j, xs.field 0], map D' f (xs.field 1)]
    | _ => panic! "out: not a description"
  --|ex
  --| sorry
  --sol>

partial def runPrim (code : Code) : Prim → Array RVal → RVal
  | .ind, #[D, m, i, x] => ind code D m i x
  | .delim, #[a, b, c, h, D] => delim code a b c h D
  | .coit, #[D, st, i, s] => .coit D st i s
  | .scofix, #[f, i, a] => .scofix f i a
  | .out, #[x] => out code x
  | .unreachable, _ => panic! "reached an impossible case"
  | .lazyTag, #[x] => match x with
    | .coit .. => .obj 1 #[]
    | .scofix .. => .obj 2 #[]
    | _ => .obj 0 #[]
  | .pack, #[D, x] => RVal.packWith (apply code) D x
  | .unpack, #[D, x] | .view .., #[D, x] => RVal.unpackWith (apply code) D x
  | .tag, #[x] => .obj (RVal.tagOf x) #[]
  | .natTag, #[x] => .obj (RVal.tagOf x) #[]
  | .natPred, #[x] => .nat (((x.toNat?).getD 1) - 1)
  | .natSucc, #[x] => .nat (((x.toNat?).getD 0) + 1)
  | .fieldAt, #[x, n] => x.field ((n.toNat?).getD 0)
  | .mkObj, #[t, fs] =>
    let rec collect (l : RVal) (acc : Array RVal) (fuel : Nat) : Array RVal :=
      match fuel, l with
      | f + 1, .obj 0 #[a, rest] => collect rest (acc.push a) f
      | _, _ => acc
    .obj (RVal.tagOf t) (collect fs #[] 100000)
  | _, _ => panic! "bad primitive application"

end

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

def RVal.tag? : RVal → Option Nat
  | .obj t _ => some t
  -- a scalar tag (as printed by compiled code)
  | .nat t => some t
  | _ => none

/-- The characters of a value of the registered `string` type,
`String.mk (List.cons (Char.mk n) …)`. -/
partial def RVal.toString? (v : RVal) : Option String := do
  let rec chars (l : RVal) (acc : String) : Option String := do
    match ← l.tag? with
    | 0 => some acc
    | _ =>
      let n ← ((l.field 0).field 0).toNat?
      chars (l.field 1) (acc.push (Char.ofNat n))
  chars (v.field 0) ""

/-- Read a runtime value back as a term of type `ty`, for printing. Numbers and
strings of the registered `nat` and `string` types print as literals. -/
partial def readback (g : Globals R) (builtins : List (Name × Name)) (ty : VTy R) (v : RVal) : Term R :=
  let readback := readback g builtins
  match whnf ty, v with
  | .mu _ _ _ _ _ (some (T, _, _)), v =>
    if builtins.lookup "nat" == some T then
      match v.toNat? with
      | some n => .const (toString n) []
      | none => readbackData ty v
    else if builtins.lookup "string" == some T then
      match v.toString? with
      | some s => .const s.quote []
      | none => readbackData ty v
    else readbackData ty v
  | .mu .., v => readbackData ty v
  | .sigma _ _ A B _, v =>
    let a' := readback A (v.field 0)
    .pair a' (readback (Closure.inst g B (eval g [] a')) (v.field 1))
  | .enum ls, .obj t _ => .tag ls t
  | .enum ls, .nat t => .tag ls t
  | .unit _, _ => .tt
  | .pi .., _ => .const "<function>" []
  | .nu .., _ => .const "<codata>" []
  | _, _ => .tt
where
  readbackData (ty : VTy R) (v : RVal) : Term R :=
    match whnf ty with
    | .mu l I D i _ _ =>
      let v := match v with
        | .nat n => if builtins.lookup "nat" == (match whnf ty with
            | .mu _ _ _ _ _ (some (T, _, _)) => some T
            | _ => none) then RVal.natView n else unflat D v
        | v => unflat D v
      .con (readback g builtins (vInterp g l I D (muFamily l I D) i) v)
    | _ => .tt
  /-- The payload of a flat value, walking the description (as a value). -/
  unflat (D : Val R) (v : RVal) : RVal :=
    let field (n : Nat) : RVal := match v with
      | .obj _ fs => fs[n]?.getD .erased
      | _ => .erased
    let rec rest (d : Val R) (n : Nat) (fuel : Nat) : RVal :=
      match fuel with
      | 0 => .erased
      | fuel + 1 =>
      match whnf d with
      | .darg _ S F =>
        let f := field n
        .obj 0 #[f, rest (vApp g F (eval g [] (readback g builtins S f))) (n + 1) fuel]
      | .drec _ _ D' | .dhrec _ _ _ D' => .obj 0 #[field n, rest D' (n + 1) fuel]
      | _ => .obj 0 #[.erased, .erased]
    match whnf D with
    | .darg _ S F =>
      match whnf S with
      | .enum ls =>
        let t := (v.tag?).getD 0
        .obj 0 #[.obj t #[], rest (vApp g F (.tag ls t)) 0 10000]
      | _ => rest D 0 10000
    | _ => rest D 0 10000

/-- The globals an erased term mentions. -/
partial def ETerm.globals (e : ETerm) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .global n => acc.push n
  | .lam _ b | .fix _ b | .proj _ b => b.globals acc
  | .app f a => a.globals (f.globals acc)
  | .letE _ v b => b.globals (v.globals acc)
  | .obj _ fs | .prim _ fs => fs.foldl (fun acc f => f.globals acc) acc
  | .case s bs => bs.foldl (fun acc b => b.globals acc) (s.globals acc)
  | _ => acc

/-- Erase the definitions reachable from `roots`. (Erasing everything would be wasteful:
recursors of big types are expensive to erase and rarely run.) -/
def compileReachableE (g : Globals R) (builtins : List (Name × Name)) (roots : List Name) :
    TCM (Code × List (Name × String)) := do
  let mut code : Code := {}
  let mut failed : List (Name × String) := []
  let mut todo := roots.toArray
  -- definitions registered as native operations
  let natives := builtins.filter fun (key, _) => key != "nat" && key != "string"
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if code.contains n then continue
    if let some (key, _) := natives.find? (·.2 == n) then
      code := code.insert n (.prim .unreachable #[.global key])
      continue
    let some d := g.find? n | continue
    -- a declaration that can't be erased yet becomes a runtime error if it is reached
    let e ← match eraseDecl g d with
      | .ok e => pure e
      | .error err => do failed := (n, toString err) :: failed; pure (.prim .unreachable #[])
    code := code.insert n e
    todo := e.globals todo
  pure (code, failed.reverse)

/-- The same, ignoring the definitions that couldn't be erased (reaching one is a
runtime error). -/
def compileReachable (g : Globals R) (builtins : List (Name × Name)) (roots : List Name) : TCM Code :=
  return (← compileReachableE g builtins roots).1

/-- Erase every global. -/
def compileAll (g : Globals R) (builtins : List (Name × Name) := []) : TCM Code :=
  compileReachable g builtins g.order.toList

end Wiz
