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
then happen in place, with no allocation. Data payloads are mostly pairs, so sizes
usually match.

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
  sorry
where
  tokenBase : Nat := 1000000

/-- The backend's optimisations, in order: reference counting, then reuse. -/
def Decl.optimize (d : Decl) : Decl :=
  let d := d.insertRC
  { d with body := insertReuse d.body }

end Wiz.IR
