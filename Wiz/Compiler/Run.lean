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
  /-- lazy coinductive values -/
  | coit (D step i s : RVal)
  | scofix (f i a : RVal)
  deriving Inhabited

namespace RVal

def arity : PapOp → Nat
  | .delimRec => 5
  | .coitK => 4
  | .scofixK => 4

def field (v : RVal) (i : Nat) : RVal :=
  match v with
  | .obj _ fs => fs[i]?.getD .erased
  | _ => .erased

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
  --|ex
  --| | t => sorry
  --sol>

partial def apply (code : Code) (f a : RVal) : RVal :=
  match f with
  | .clo env b => run code (a :: env) b
  | .fixv env b => apply code (run code (.fixv env b :: env) b) a
  | .pap op args =>
    let args := args.push a
    if args.size < RVal.arity op then .pap op args else firePap code op args
  | _ => .erased

partial def applyN (code : Code) (f : RVal) (as : List RVal) : RVal := as.foldl (apply code) f

partial def firePap (code : Code) : PapOp → Array RVal → RVal
  | .delimRec, #[mret, marg, mrec, F, s] => delim code mret marg mrec (apply code F s)
  | .coitK, #[D, step, j, s] => .coit D step j s
  | .scofixK, #[f, _, i, a] => .scofix f i a
  | _, _ => panic! "bad partial application"

/-- **Exercise 5.3a.** `ind D m i x = m i x (hyps D x)`, where `hyps` walks the description
alongside the payload, recursing at each `rec` field (see the module docstring). -/
partial def ind (code : Code) (D m i x : RVal) : RVal :=
  --<sol
  applyN code m [i, x, hyps D x]
where
  hyps (d xs : RVal) : RVal :=
    match d with
    | .obj 0 _ => .erased
    | .obj 1 #[_, F] => hyps (apply code F (xs.field 0)) (xs.field 1)
    | .obj 2 #[j, D'] => .obj 0 #[ind code D m j (xs.field 0), hyps D' (xs.field 1)]
    | _ => panic! "ind: not a description"
  --|ex
  --| sorry
  --sol>

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
  --<sol
  match x with
  | .coit D step i s => map D (.pap .coitK #[D, step]) (applyN code step [i, s])
  | .scofix f i a => out code (applyN code f [.erased, .pap .scofixK #[f], i, a])
  | v => v
where
  map (d f xs : RVal) : RVal :=
    match d with
    | .obj 0 _ => xs
    | .obj 1 #[_, F] => .obj 0 #[xs.field 0, map (apply code F (xs.field 0)) f (xs.field 1)]
    | .obj 2 #[j, D'] => .obj 0 #[applyN code f [j, xs.field 0], map D' f (xs.field 1)]
    | _ => panic! "out: not a description"
  --|ex
  --| sorry
  --sol>

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

/-- Read a runtime value back as a term of type `ty`, for printing. -/
partial def readback (g : Globals R) (ty : VTy R) (v : RVal) : Term R :=
  match ty, v with
  | .mu l I D i _ _, v => .con (readback g (vInterp g l I D (muFamily l I D) i) v)
  | .sigma _ _ A B, .obj _ #[a, b] =>
    let a' := readback g A a
    .pair a' (readback g (Closure.inst g B (eval g [] a')) b)
  | .enum ls, .obj t _ => .tag ls t
  | .unit _, _ => .tt
  | .pi .., _ => .const "<function>" []
  | .nu .., _ => .const "<codata>" []
  | _, _ => .tt

/-- Erase every definition the term depends on (all globals, in order). -/
def compileAll (g : Globals R) : TCM Code := do
  let mut code : Code := {}
  for n in g.order do
    if let some d := g.find? n then
      -- a declaration that can't be erased yet becomes a runtime error if it is reached
      let e := match eraseDecl g d with
        | .ok e => e
        | .error _ => .prim .unreachable #[]
      code := code.insert n e
  pure code

end Wiz
