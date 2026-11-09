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

/-- The backend's optimisations, in order: dead code, reference counting, then reuse. -/
def Decl.optimize (d : Decl) : Decl :=
  let d := { d with body := (elimDead d.body).1 }
  let d := d.insertRC
  { d with body := insertReuse (dropScalars d.body) }

end Wiz.IR
