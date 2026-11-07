import Wiz.Compiler.Erase

/-!
# The IR

A first-order language in A-normal form, the input of the backends (stage 8). Every
intermediate value has a name, functions are top level (lambdas are lifted, so closures
are explicit: `pap f xs` is `f` partially applied), and control flow is `case` on a
tag, join points and tail jumps.

Values are **objects** (a tag and fields, reference counted) or **scalars**: numbers,
`◾`, and constructors without fields (`ctor t #[]` is the scalar `t`, so tags cost no
allocation). Following Perceus (Reinking, Xie, de Moura & Leijen, *Perceus: Garbage
Free Reference Counting with Reuse*, PLDI 2021), reference counts are explicit:
`dup x` and `drop x`, inserted by `RC.lean`. Every variable is **owned**: using it
as an argument transfers that reference. `proj` returns a new (owned) reference to the
field.
-/

namespace Wiz.IR

abbrev Var := Nat
abbrev JoinId := Nat

inductive Expr where
  /-- `◾`, a scalar -/
  | erased
  /-- a number (a scalar, or a big number object) -/
  | lit (n : Nat)
  /-- an object with a tag and fields; with no fields, the scalar `tag` -/
  | ctor (tag : Nat) (args : Array Var)
  /-- field `i` of `x` (a new reference) -/
  | proj (i : Nat) (x : Var)
  /-- full application of a top-level function -/
  | fap (f : Name) (args : Array Var)
  /-- partial application: a closure -/
  | pap (f : Name) (args : Array Var)
  /-- apply a closure -/
  | ap (f : Var) (args : Array Var)
  /-- a runtime operation: `nat.add` …, `lazyTag` -/
  | prim (op : Name) (args : Array Var)
  deriving Repr, Inhabited, BEq

inductive Body where
  | vdecl (x : Var) (e : Expr) (b : Body)
  /-- branch on the tag of `x` (an object's tag, or a scalar's value) -/
  | case (x : Var) (alts : Array Body)
  | ret (x : Var)
  /-- `join j(params) := body; k`: `body` may only use its parameters -/
  | jdecl (j : JoinId) (params : Array Var) (body : Body) (k : Body)
  | jmp (j : JoinId) (args : Array Var)
  | dup (x : Var) (b : Body)
  | drop (x : Var) (b : Body)
  | unreachable
  deriving Repr, Inhabited

structure Decl where
  name : Name
  params : Array Var
  body : Body
  deriving Repr, Inhabited

namespace Expr

def args : Expr → Array Var
  | ctor _ as | fap _ as | pap _ as | prim _ as => as
  | ap f as => #[f] ++ as
  | proj _ x => #[x]
  | _ => #[]

def toString : Expr → String
  | erased => "◾"
  | lit n => s!"{n}"
  | ctor t as => if as.isEmpty then s!"{t}" else s!"ctor {t} {vs as}"
  | proj i x => s!"proj {i} x{x}"
  | fap f as => s!"{f} {vs as}"
  | pap f as => s!"pap {f} {vs as}"
  | ap f as => s!"ap x{f} {vs as}"
  | prim op as => s!"prim {op} {vs as}"
where
  vs (as : Array Var) : String := " ".intercalate (as.toList.map (s!"x{·}"))

end Expr

namespace Body

/-- The free variables of a body. -/
partial def freeVars (b : Body) : Std.HashSet Var :=
  go b {}
where
  go : Body → Std.HashSet Var → Std.HashSet Var
    | vdecl x e b, acc => (e.args.foldl (·.insert ·) ((go b acc).erase x))
    | case x alts, acc => alts.foldl (fun acc a => go a acc) (acc.insert x)
    | ret x, acc => acc.insert x
    | jdecl _ ps body k, acc =>
      let accB := ps.foldl (·.erase ·) (go body {})
      accB.fold (·.insert ·) (go k acc)
    | jmp _ as, acc => as.foldl (·.insert ·) acc
    | dup x b, acc | drop x b, acc => (go b acc).insert x
    | unreachable, acc => acc

partial def toString (b : Body) (ind : String := "  ") : String :=
  match b with
  | vdecl x e b => s!"{ind}let x{x} := {e.toString}\n{b.toString ind}"
  | case x alts =>
    let as := alts.toList.zipIdx.map fun (a, i) => s!"{ind}| {i} =>\n{a.toString (ind ++ "    ")}"
    s!"{ind}case x{x} of\n{"\n".intercalate as}"
  | ret x => s!"{ind}ret x{x}"
  | jdecl j ps body k =>
    s!"{ind}join j{j}({Expr.toString.vs ps}) :=\n{body.toString (ind ++ "    ")}\n{k.toString ind}"
  | jmp j as => s!"{ind}jmp j{j} {Expr.toString.vs as}"
  | dup x b => s!"{ind}dup x{x}\n{b.toString ind}"
  | drop x b => s!"{ind}drop x{x}\n{b.toString ind}"
  | unreachable => s!"{ind}unreachable"

end Body

def Decl.toString (d : Decl) : String :=
  s!"def {d.name} {Expr.toString.vs d.params} :=\n{d.body.toString}"

end Wiz.IR
