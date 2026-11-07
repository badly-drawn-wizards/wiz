import Wiz.Compiler.IR

/-!
# Reference counting (Perceus)

Insert `dup` and `drop` so that every reference is consumed exactly once
(Reinking et al., *Perceus*, PLDI 2021). Every variable is **owned** when it is
bound, and must be either passed on (as an argument, a returned value, or a jump
argument) or dropped:

* an argument that is still needed afterwards (or appears again in the same call) is
  `dup`ed first; otherwise the call takes over the reference;
* a variable is dropped **as soon as it is dead**: right after the binding that last
  used it, at the start of each `case` branch that doesn't use it, or at the start of
  the function if it is never used. This is what makes Perceus garbage free: no
  object is kept alive longer than its last use;
* `proj` doesn't consume the object (it returns a new reference to the field).

Join point bodies only use their parameters (see `Lower.lean`), so they start from
their own parameters.

Not done yet: borrowed parameters, drop specialisation and reuse (`8c`).
-/

namespace Wiz.IR

/-- Prefix `b` with drops of the owned variables not used in it. -/
def dropDead (owned : Std.HashSet Var) (live : Std.HashSet Var) (b : Body) : Body × Std.HashSet Var :=
  let dead := (owned.toArray.filter (!live.contains ·)).qsort (· < ·)
  (dead.foldr (fun x acc => .drop x acc) b, dead.foldl (·.erase ·) owned)

/-- **Exercise 8.1.** Insert reference counting operations into `b`, where `owned` are
the variables currently holding a reference (see the module docstring). For a call
with arguments `as`, walk them left to right: an argument that is not owned, still live
in the rest of the body, or used again later in `as`, gets a `dup`; otherwise its
reference moves into the call. -/
partial def insertRC (owned : Std.HashSet Var) (b : Body) : Body :=
  sorry

/-- Reference counting for a function: its parameters are owned. -/
def Decl.insertRC (d : Decl) : Decl :=
  let owned : Std.HashSet Var := d.params.foldl (·.insert ·) {}
  let live := d.body.freeVars
  let (body, _) := dropDead owned live (Wiz.IR.insertRC (owned.filter live.contains) d.body)
  { d with body }

end Wiz.IR
