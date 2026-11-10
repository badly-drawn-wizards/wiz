import Wiz.Compiler.IR

/-!
# Reference counting (Perceus)

Insert `dup` and `drop` so that every reference is consumed exactly once
(Reinking et al., *Perceus*, PLDI 2021). A variable is **owned** when it is bound
(it holds a reference), and must be either passed on (as an argument, a returned value,
or a jump argument) or dropped:

* an argument that is still needed afterwards (or appears again in the same call) is
  `dup`ed first; otherwise the call takes over the reference;
* a variable is dropped **as soon as it is dead**: right after the binding that last
  used it, at the start of each `case` branch that doesn't use it, or at the start of
  the function if it is never used. This is what makes Perceus garbage free: no
  object is kept alive longer than its last use;
* `proj` doesn't consume the object, and reads the field without a new reference: the
  field of an owned object is `dup`ed at once (it may outlive the object), the field of
  a borrowed one is borrowed too.

**Borrowed parameters** (stage 8e, as in Lean 4): a parameter the function never
consumes is *borrowed*: the caller keeps its reference and lends it for the call, so
neither side counts. `Borrow.lean` decides which parameters are borrowed; here a
borrowed variable is simply one that is not owned: it is `dup`ed when it is consumed and
never dropped. At a call, an argument in a borrowed position is lent (not consumed); a
variable lent to a call and also passed to an owned position of the same call is
`dup`ed for the owned one (the callee might free it while the borrow is still used).
Join points have borrowed parameters too.

Join point bodies only use their parameters (see `Lower.lean`), so they start from
their own parameters.
-/

namespace Wiz.IR

/-- Which parameters are borrowed: of the functions of the program and of the join
points of the current function (absent: all owned). -/
structure BorrowSigs where
  fns : Std.HashMap Name (Array Bool) := {}
  jps : Std.HashMap JoinId (Array Bool) := {}
  deriving Inhabited

/-- Is parameter `i` of `f` borrowed? -/
def BorrowSigs.fn (σ : BorrowSigs) (f : Name) (i : Nat) : Bool :=
  ((σ.fns.get? f).bind (·[i]?)).getD false

/-- Is parameter `i` of join point `j` borrowed? -/
def BorrowSigs.jp (σ : BorrowSigs) (j : JoinId) (i : Nat) : Bool :=
  ((σ.jps.get? j).bind (·[i]?)).getD false

/-- Prefix `b` with drops of the owned variables not used in it. -/
def dropDead (owned : Std.HashSet Var) (live : Std.HashSet Var) (b : Body) : Body × Std.HashSet Var :=
  let dead := (owned.toArray.filter (!live.contains ·)).qsort (· < ·)
  (dead.foldr (fun x acc => .drop x acc) b, dead.foldl (·.erase ·) owned)

/-- The arguments of an expression in owned positions (consumed), and those lent to
borrowed positions. -/
def splitArgs (σ : BorrowSigs) : Expr → Array Var × Array Var
  | .proj _ _ => (#[], #[])
  | .fap f as =>
    (as.zipIdx.filterMap fun (a, i) => if σ.fn f i then none else some a,
     as.zipIdx.filterMap fun (a, i) => if σ.fn f i then some a else none)
  | e => (e.args, #[])

/-- **Exercise 8.1.** Insert reference counting operations into `b`, where `owned` are
the variables currently holding a reference (see the module docstring). For a call
with arguments `as`, walk them left to right: an argument that is not owned, still live
in the rest of the body, or used again later in `as`, gets a `dup`; otherwise its
reference moves into the call. `σ` says which arguments are only lent (stage 8e; with
the empty `σ`, none are). -/
partial def insertRC (σ : BorrowSigs) (owned : Std.HashSet Var) (b : Body) : Body :=
  --<sol
  match b with
  | .vdecl x (.proj i y) rest =>
    let live := rest.freeVars
    -- the field of an owned object becomes ours (`dup`ed before the object may be
    -- dropped); the field of a borrowed one is borrowed
    let mine := owned.contains y && live.contains x
    let owned := if mine then owned.insert x else owned
    let (rest', _) := dropDead owned live (insertRC σ (owned.filter live.contains) rest)
    .vdecl x (.proj i y) (if mine then .dup x rest' else rest')
  | .vdecl x e rest =>
    let live := rest.freeVars
    -- the arguments the expression consumes, and those it borrows
    let (consumed, lent) := splitArgs σ e
    let (dups, owned) := consume owned (lent.foldl (·.insert ·) live) consumed
    let owned := owned.insert x
    let (rest', _) := dropDead owned live (insertRC σ (owned.filter live.contains) rest)
    dups.foldr (fun y acc => .dup y acc) (.vdecl x e rest')
  | .case x alts =>
    .case x (alts.map fun alt =>
      let (alt', _) := dropDead owned alt.freeVars (insertRC σ (owned.filter alt.freeVars.contains) alt)
      alt')
  | .ret x =>
    let (dups, owned) := consume owned {} #[x]
    let (b', _) := dropDead owned {} (.ret x)
    dups.foldr (fun y acc => .dup y acc) b'
  | .jdecl j ps body k =>
    let ownedB : Std.HashSet Var := ps.zipIdx.foldl (fun s (p, i) => if σ.jp j i then s else s.insert p) {}
    let (body', _) := dropDead ownedB body.freeVars (insertRC σ (ownedB.filter body.freeVars.contains) body)
    .jdecl j ps body' (insertRC σ owned k)
  | .jmp j as =>
    let consumed := as.zipIdx.filterMap fun (a, i) => if σ.jp j i then none else some a
    let lent : Std.HashSet Var := as.zipIdx.foldl (fun s (a, i) => if σ.jp j i then s.insert a else s) {}
    let (dups, owned) := consume owned lent consumed
    let (b', _) := dropDead owned lent (.jmp j as)
    dups.foldr (fun y acc => .dup y acc) b'
  | b => b
where
  /-- Consume `as` in order: returns the variables to `dup` first, and what stays owned. -/
  consume (owned : Std.HashSet Var) (live : Std.HashSet Var) (as : Array Var) : Array Var × Std.HashSet Var :=
    Id.run do
      let mut owned := owned
      let mut dups := #[]
      for a in as, i in [0:as.size] do
        let usedLater := live.contains a || (as.extract (i + 1) as.size).contains a
        if owned.contains a && !usedLater then owned := owned.erase a
        else dups := dups.push a
      pure (dups, owned)
  --|ex
  --| sorry
  --sol>

/-- Reference counting for a function: its parameters are owned, except those `σ` says
are borrowed. -/
def Decl.insertRC (d : Decl) (σ : BorrowSigs := {}) : Decl :=
  let owned : Std.HashSet Var :=
    d.params.zipIdx.foldl (fun s (p, i) => if σ.fn d.name i then s else s.insert p) {}
  let live := d.body.freeVars
  let (body, _) := dropDead owned live (Wiz.IR.insertRC σ (owned.filter live.contains) d.body)
  { d with body, borrow := d.params.zipIdx.map fun (_, i) => σ.fn d.name i }

end Wiz.IR
