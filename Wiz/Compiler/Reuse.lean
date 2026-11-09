import Wiz.Compiler.RC

/-!
# Reuse (Perceus, part 2)

After reference counting, a `drop x` followed (in the same block) by an allocation
`ctor t args` can **reuse** `x`'s memory: if `x` is unique at runtime, dropping it would
free a cell that the allocation could have. So

    drop x; …; let y := ctor t args        ↦        let w := reset x; …; let y := reuse w in ctor t args

`reset x` drops `x`'s fields and keeps its cell when `x` is unique (and just drops `x`
otherwise); `reuse` writes the new object into the cell if it has the same size, and
allocates if not. Functional updates of unique data (mapping over a list you own)
then happen in place, with no allocation. The constructors of a type often have the same number of fields (the
`cons` cells of a list always do), so sizes often match.

Only allocations in the same block are paired (not across `case` or join points), so
each token is used exactly once.
-/

namespace Wiz.IR

/-- Replace the first plain allocation with fields in the straight-line prefix of `b` by a
reuse of `tok`. -/
partial def claimCtor (tok : Var) : Body → Option Body
  | .vdecl y (.ctor t as) rest =>
    if as.isEmpty then (claimCtor tok rest).map (.vdecl y (.ctor t as) ·)
    else some (.vdecl y (.reuse tok t as) rest)
  | .vdecl y e rest => (claimCtor tok rest).map (.vdecl y e ·)
  | .dup x rest => (claimCtor tok rest).map (.dup x ·)
  | .drop x rest => (claimCtor tok rest).map (.drop x ·)
  | _ => none

/-- **Exercise 8.3.** Pair drops with later allocations (inner ones first). The token
for `drop x` is the variable `tokenBase + x`. -/
partial def insertReuse (b : Body) : Body :=
  --<sol
  match b with
  | .drop x rest =>
    let rest := insertReuse rest
    let tok := tokenBase + x
    match claimCtor tok rest with
    | some rest' => .vdecl tok (.reset x) rest'
    | none => .drop x rest
  | .vdecl x e rest => .vdecl x e (insertReuse rest)
  | .dup x rest => .dup x (insertReuse rest)
  | .case x alts => .case x (alts.map insertReuse)
  | .jdecl j ps body k => .jdecl j ps (insertReuse body) (insertReuse k)
  | b => b
  --|ex
  --| sorry
  --sol>
where
  tokenBase : Nat := 1000000

/-- Scalars (`◾`, small numbers, constructors without fields) have no reference count:
remove the `dup`s and `drop`s of variables bound to them, so that they don't become
`reset`s either. -/
partial def dropScalars (b : Body) (sc : Std.HashSet Var := {}) : Body :=
  match b with
  | .vdecl x e rest =>
    let scalar := match e with
      | .erased => true
      | .lit n => n < 2 ^ 62
      | .ctor _ as => as.isEmpty
      | _ => false
    .vdecl x e (dropScalars rest (if scalar then sc.insert x else sc))
  | .dup x rest => if sc.contains x then dropScalars rest sc else .dup x (dropScalars rest sc)
  | .drop x rest => if sc.contains x then dropScalars rest sc else .drop x (dropScalars rest sc)
  | .case x alts => .case x (alts.map (dropScalars · sc))
  | .jdecl j ps body k => .jdecl j ps (dropScalars body sc) (dropScalars k sc)
  | b => b

/-- Dead code: a pure value nobody uses, dropped before reference counting (erasure
leaves some behind, like a pair of erased proofs, or a field read for a pattern
variable the branch never mentions; each was an allocation, or an increment and a
decrement, on every call). Returns the body and its free variables. -/
partial def elimDead : Body → Body × Std.HashSet Var
  | .vdecl x e rest =>
    let (rest', fv) := elimDead rest
    let pure := match e with
      | .erased | .lit _ | .ctor _ _ | .proj _ _ | .pap _ _ => true
      | _ => false
    if pure && !fv.contains x then (rest', fv)
    else (.vdecl x e rest', e.args.foldl (·.insert ·) (fv.erase x))
  | .case x alts =>
    let rs := alts.map elimDead
    (.case x (rs.map (·.1)), rs.foldl (fun acc r => r.2.fold (·.insert ·) acc) ({} : Std.HashSet Var) |>.insert x)
  | .jdecl j ps body k =>
    let (body', fb) := elimDead body
    let (k', fk) := elimDead k
    (.jdecl j ps body' k', (ps.foldl (·.erase ·) fb).fold (·.insert ·) fk)
  | .ret x => (.ret x, ({} : Std.HashSet Var).insert x)
  | .jmp j as => (.jmp j as, as.foldl (·.insert ·) {})
  | .dup x b => let (b', f) := elimDead b; (.dup x b', f.insert x)
  | .drop x b => let (b', f) := elimDead b; (.drop x b', f.insert x)
  | .unreachable => (.unreachable, {})

/-- A closed constant: built from numbers, `◾` and constructors only. A constructor node
caches its hash, computed from its children's (so hashing is O(1) and interning every
node of a constant is linear in its size); build one only with `Const.mkCtor`, which
computes it. -/
inductive Const where
  | erased
  | lit (n : Nat)
  | ctor (tag : Nat) (args : Array Const) (cachedHash : UInt64)
  deriving Inhabited

namespace Const

def hash : Const → UInt64
  | erased => 7
  | lit n => mixHash 13 (Hashable.hash n)
  | ctor _ _ h => h

/-- The only way to build a constructor node: its hash from its tag and its children's. -/
def mkCtor (t : Nat) (args : Array Const) : Const :=
  .ctor t args (args.foldl (fun h a => mixHash h a.hash) (mixHash 17 (Hashable.hash t)))

instance : Hashable Const := ⟨Const.hash⟩

/-- Equal constants: the cached hashes first (unequal ones differ at once), then the
structure. -/
partial def beq (a b : Const) : Bool :=
  a.hash == b.hash && match a, b with
    | erased, erased => true
    | lit m, lit n => m == n
    | ctor t as _, ctor u bs _ => t == u && as.size == bs.size && (as.zip bs).all fun (x, y) => beq x y
    | _, _ => false

instance : BEq Const := ⟨Const.beq⟩

end Const

/-- Constants hoisted out of the functions (a string literal is a list of characters,
and was built again at every use): each closed constant constructor becomes a call of a
function `wiz.const.k` without parameters, which the C backend runs once (other
backends just call it). The constants are numbered in a table, equal ones once. -/
structure Hoist where
  table : Std.HashMap Const Name := {}
  decls : Array Decl := #[]

/-- The body that builds a constant, in A-normal form, from variable `next` on. -/
partial def Const.build (c : Const) (next : Var) : Body × Var × Var :=
  match c with
  | .erased => (.vdecl next .erased (.ret next), next, next + 1)
  | .lit n => (.vdecl next (.lit n) (.ret next), next, next + 1)
  | .ctor t args _ =>
    -- the arguments first, then the constructor
    let (wrap, vs, n) := args.foldl (fun (acc : (Body → Body) × Array Var × Var) a =>
      let (w, vs, n) := acc
      let (b, v, n') := a.build n
      (fun k => w (splice b k), vs.push v, n')) ((fun k => k), #[], next)
    (wrap (.vdecl n (.ctor t vs) (.ret n)), n, n + 1)
where
  -- replace the final `ret` of a straight-line body by `k`
  splice : Body → Body → Body
    | .vdecl x e b, k => match b with
      | .ret _ => .vdecl x e k
      | _ => .vdecl x e (splice b k)
    | b, _ => b

/-- The variables a body uses other than as the field of a constant constructor (`roots`
are the constants needed as values: only those are hoisted, so a string's suffixes don't
each get a function, and each constant is hashed and built once). -/
partial def valueUses (consts : Std.HashSet Var) : Body → Std.HashSet Var → Std.HashSet Var
  | .vdecl x e rest, acc =>
    let acc := valueUses consts rest acc
    match e with
    | .ctor _ _ => if consts.contains x then acc else e.args.foldl (·.insert ·) acc
    | _ => e.args.foldl (·.insert ·) acc
  | .case x alts, acc => alts.foldl (fun acc a => valueUses consts a acc) (acc.insert x)
  | .jdecl _ _ body k, acc => valueUses consts k (valueUses consts body acc)
  | .ret x, acc => acc.insert x
  | .jmp _ as, acc => as.foldl (·.insert ·) acc
  | .dup x b, acc | .drop x b, acc => valueUses consts b (acc.insert x)
  | .unreachable, acc => acc

/-- The constant variables of a body, and their trees. -/
partial def constVars (consts : Std.HashMap Var Const) : Body → Std.HashMap Var Const
  | .vdecl x e rest =>
    let c? : Option Const := match e with
      | .erased => some .erased
      | .lit n => some (.lit n)
      | .ctor t as => if as.all consts.contains then some (Const.mkCtor t (as.map (consts.getD · .erased))) else none
      | _ => none
    constVars (match c? with | some c => consts.insert x c | none => consts) rest
  | .case _ alts => alts.foldl (fun acc a => constVars acc a) consts
  | .jdecl _ _ body k => constVars (constVars consts body) k
  | _ => consts

partial def hoistBody (st : Hoist) (consts : Std.HashMap Var Const) (roots : Std.HashSet Var) : Body → Hoist × Body
  | .vdecl x e rest =>
    let (st, e') := match e with
      | .ctor _ as =>
        if as.isEmpty || !roots.contains x then (st, e) else
        match consts.get? x with
        | none => (st, e)
        | some c => match st.table.get? c with
          | some n => (st, Expr.fap n #[])
          | none =>
            let n := s!"wiz.const.{st.decls.size}"
            let (b, _, _) := c.build 0
            ({ table := st.table.insert c n, decls := st.decls.push { name := n, params := #[], body := b } },
              Expr.fap n #[])
      | _ => (st, e)
    let (st, rest') := hoistBody st consts roots rest
    (st, .vdecl x e' rest')
  | .case x alts =>
    let (st, alts') := alts.foldl (fun (acc : Hoist × Array Body) a =>
      let (st, bs) := acc
      let (st, a') := hoistBody st consts roots a
      (st, bs.push a')) (st, #[])
    (st, .case x alts')
  | .jdecl j ps body k =>
    let (st, body') := hoistBody st consts roots body
    let (st, k') := hoistBody st consts roots k
    (st, .jdecl j ps body' k')
  | b => (st, b)

def hoistConsts (decls : Array Decl) : Array Decl :=
  let (st, ds) := decls.foldl (fun (acc : Hoist × Array Decl) d =>
    let (st, ds) := acc
    let consts := constVars {} d.body
    let roots := valueUses (consts.fold (fun acc x _ => acc.insert x) {}) d.body {}
    let (st, b) := hoistBody st consts roots d.body
    (st, ds.push { d with body := b })) ({}, #[])
  ds ++ st.decls

/-- The backend's optimisations, in order: dead code, reference counting, then reuse. -/
def Decl.optimize (d : Decl) : Decl :=
  let d := { d with body := (elimDead d.body).1 }
  let d := d.insertRC
  { d with body := insertReuse (dropScalars d.body) }

end Wiz.IR
