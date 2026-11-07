import Wiz.Compiler.Erase

/-!
# Running erased programs

An environment-based interpreter for `ETerm`. Strict (call-by-value), except that
coinductive values (`coit`, `scofix`) are lazy and unfold only under `out`.

The generic eliminators are **primitives that walk the description** at runtime. A
description is an ordinary runtime value: `⟨0 i⟩` (ret), `⟨1 ◾ F⟩` (arg), `⟨2 j D⟩`
(rec). A data value is its payload of nested pairs, `⟨0 tag ⟨0 f₁ … ⟩⟩`.

    ind D m i x      = m i x (hyps D x),   hyps (rec j D') ⟨y, r⟩ = ⟨ind D m j y, hyps D' r⟩
    out (coit D step i s) = map D (coit D step) i (step i s)

`#eval` reads a value back into a term using its **type**, so results print with
constructor names.
-/

namespace Wiz

/-- Partially applied runtime primitives (closures the runtime itself creates). -/
inductive PapOp where
  /-- `fun s => delim mret marg mrec (F s)`: args `mret marg mrec F`, arity 1 -/
  | delimRec
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
  | .delimRec => 5
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
  | .obj 0 #[.obj 0 #[], _] => some 0
  | .obj 0 #[.obj 1 #[], .obj 0 #[k, _]] => (toNat? k).map (· + 1)
  | _ => none

def nativeArity : Name → Nat
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
  | t => sorry

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
  | "nat.beq" => .obj 0 #[.obj (if n 0 == n 1 then 1 else 0) #[], .obj 0 #[.erased, .erased]]
  | _ => panic! s!"unknown native operation {op}"

partial def applyN (code : Code) (f : RVal) (as : List RVal) : RVal := as.foldl (apply code) f

partial def firePap (code : Code) : PapOp → Array RVal → RVal
  | .delimRec, #[mret, marg, mrec, F, s] => delim code mret marg mrec (apply code F s)
  | .coitK, #[D, step, j, s] => .coit D step j s
  | .scofixK, #[f, _, i, a] => .scofix f i a
  | _, _ => panic! "bad partial application"

/-- **Exercise 5.3a.** `ind D m i x = m i x (hyps D x)`, where `hyps` walks the description
alongside the payload, recursing at each `rec` field (see the module docstring). -/
partial def ind (code : Code) (D m i x : RVal) : RVal :=
  sorry

partial def delim (code : Code) (mret marg mrec D : RVal) : RVal :=
  match D with
  | .obj 0 #[i] => apply code mret i
  | .obj 1 #[_, F] => applyN code marg [.erased, .erased, F, .pap .delimRec #[mret, marg, mrec, F]]
  | .obj 2 #[j, D'] => applyN code mrec [.erased, j, D', delim code mret marg mrec D']
  | _ => panic! "Desc.elim: not a description"

/-- **Exercise 5.3b.** Observe a coinductive value. A `coit` runs one step and re-wraps
the recursive positions (`map`); an `scofix` unfolds once; anything else (a `cocon`,
whose erased form is its payload) is already observed. -/
partial def out (code : Code) (x : RVal) : RVal :=
  sorry

partial def runPrim (code : Code) : Prim → Array RVal → RVal
  | .ind, #[D, m, i, x] => ind code D m i x
  | .delim, #[a, b, c, D] => delim code a b c D
  | .coit, #[D, st, i, s] => .coit D st i s
  | .scofix, #[f, i, a] => .scofix f i a
  | .out, #[x] => out code x
  | .unreachable, _ => panic! "reached an impossible case"
  | _, _ => panic! "bad primitive application"

end

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

def RVal.tag? : RVal → Option Nat
  | .obj t _ => some t
  | .nat 0 => some 0
  | .nat _ => some 1
  | _ => none

/-- The characters of a value of the registered `string` type,
`String.mk (List.cons (Char.mk n) …)`. -/
partial def RVal.toString? (v : RVal) : Option String := do
  let rec chars (l : RVal) (acc : String) : Option String := do
    match ← (l.field 0).tag? with
    | 0 => some acc
    | _ =>
      let n ← (((l.field 1).field 0).field 1).field 0 |>.toNat?
      chars (((l.field 1).field 1).field 0) (acc.push (Char.ofNat n))
  chars ((v.field 1).field 0) ""

/-- Read a runtime value back as a term of type `ty`, for printing. Numbers and
strings of the registered `nat` and `string` types print as literals. -/
partial def readback (g : Globals R) (builtins : List (Name × Name)) (ty : VTy R) (v : RVal) : Term R :=
  let readback := readback g builtins
  match ty, v with
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
  | .sigma _ _ A B, v =>
    let a' := readback A (v.field 0)
    .pair a' (readback (Closure.inst g B (eval g [] a')) (v.field 1))
  | .enum ls, .obj t _ => .tag ls t
  | .unit _, _ => .tt
  | .pi .., _ => .const "<function>" []
  | .nu .., _ => .const "<codata>" []
  | _, _ => .tt
where
  readbackData (ty : VTy R) (v : RVal) : Term R :=
    match ty with
    | .mu l I D i _ _ =>
      let v := match v with
        | .nat n => RVal.natView n
        | v => v
      .con (readback g builtins (vInterp g l I D (muFamily l I D) i) v)
    | _ => .tt

/-- Erase every definition the term depends on (all globals, in order). -/
def compileAll (g : Globals R) (builtins : List (Name × Name) := []) : TCM Code := do
  let mut code : Code := {}
  for n in g.order do
    if let some d := g.find? n then
      -- a declaration that can't be erased yet becomes a runtime error if it is reached
      let e := match eraseDecl g d with
        | .ok e => e
        | .error _ => .prim .unreachable #[]
      code := code.insert n e
  -- definitions registered as native operations
  for (key, n) in builtins do
    if key != "nat" then code := code.insert n (.prim .unreachable #[.global key])
  pure code

end Wiz
