# wiz-rs: surface sketch and lowering rules (hand-lowering, before the front end exists)

Plan: `/workspace/wiz-notes/rust-dsl-plan.md`, `borrows-as-optics.md`, `uniqueness.md`.
Decisions RD1–RD16 are the user's (roadmap memory). This file pins down what the front end
(a Wiz command macro, RD4) must emit; `lowered/NN_*.wiz` were written by following these
rules literally, and they check (`sh drafts/rust/check.sh`).

Files:

| path | what | checks? |
|---|---|---|
| `lib/Optic.wiz` | `Result`/`Error` (RD7), `Store`, `Lens`, `PLens`, `Affine`, `zoom`, `TraverseMut`, laws, proofs | yes, tested (`lake test -- optic`) |
| `drafts/rust/lib/RsCore.wiz` | regions, `Shr`/`Mut`/`MutOpt`, `Flow`, Nat-backed `U64` and List-backed `Vec` stand-ins | yes (stand-ins for agent/natives-ints and agent/vec-lib) |
| `drafts/rust/surface/NN_*.wiz` | the programs in the DSL's surface syntax | no (wishful) |
| `drafts/rust/lowered/NN_*.wiz` | the same programs, hand-lowered | yes, with `#eval`s |
| `drafts/rust/Optic.wiz` | the part of the optics library that doesn't check yet | no (wishful) |

## 1. The surface, sketched (RD5: closer to Wiz than to Rust; Rust's semantics)

```
import Rust
rust
  struct Stats where                       -- like a Wiz structure: one field per line
    hits : U64
    misses : U64
  enum Tree where                          -- like a Wiz inductive; recursion through Box
    | leaf
    | node (key : U64) (left : Box Tree) (right : Box Tree)

  fn get_mut {'a} (v : &'a mut Vec U64) (i : USize) : &'a mut U64   -- Wiz binders; region params in braces
    requires i < v.len                     -- RD13 clauses between the signature and :=
    ensures final(v) = old(v).set i final(result)
  := &mut v[i]

  fn sum_from (s0 : U64) (n : U64) : Result U64 Overflow := {        -- a block: statements separated by ;
    let mut i : U64 := 0;                  -- let / let mut, Wiz's :=
    let mut s := s0;
    while i < n invariant … decreases n - i do {
      s := (s.checked_add i).ok_or Overflow ?;    -- assignment is :=, compound += etc.; postfix ?
      i += 1
    };
    .ok s                                  -- the block's value; `return e` also exists
  }
end
```

| construct | surface | notes |
|---|---|---|
| items | `fn`, `struct … where`, `enum … where`, (later `impl`, `trait`) | inside `rust … end` (one command macro per block) |
| binders | `(x : T)`, `{T : Type}`, `{'a 'b}`, `[Tr T]` | as Wiz; `'a` is a region (lifetime) |
| types | `U64`, `USize`, `Bool`, `Vec T`, `Box T`, `Option T`, `Result T E`, `&'a T`, `&'a mut T`, `A × B` | Wiz-style application, not `Vec<T>`; `'a` may be elided |
| statements | `let x := e`, `let mut x : T := e`, `p := e`, `p += e`, `e;` | places `p`: `x`, `*r`, `p.f`, `p[i]` |
| expressions | `if c then a else b`, `match e with \| .c x => …`, `if let .c x := e then … else …`, `{ … }`, `e ?`, `return e`, `&e`, `&mut e`, `*e`, method calls `v.push x` | `match` is Wiz's (alternatives with `\|`, `.c` constructors) |
| loops | `while c do { }`, `while let p := e do { }`, `loop { }`, `for i in a..b do e`, `break`, `continue`, clauses `invariant`/`decreases` | |
| calls | `f x y` (curried look), saturated from the first `&mut` argument on (RD5) | `f (&mut a) b`; partial application only before the first `&mut` |
| library | `mem.swap`, `mem.replace`, `mem.take`, `Vec.new`, `v.push`, `v.len`, `v.get_mut i`, `x.checked_add y`, `o.ok_or e` | Rust's std names, Wiz's dot style |
| specs | `requires`, `ensures` (with `result`, `old(x)`, `final(x)`), `invariant`, `decreases` | RD13; lowered to quantity-0 Props |

Why Wiz-like: the DSL is a teaching device for Rust's *semantics* (moves, borrows,
in-place mutation), read next to its lowering; sharing Wiz's binders, `match` and
constructor syntax keeps the two side by side readable (RD1, RD5).

## 2. Lowering rules

Notation: `⟦e⟧` the lowering; `R A` is `Result A` (lib/Optic.wiz).

**L1. Items and generics.** `fn f {'a} {T : Type} [C T] (xs…) : Ret` ↦
`def f {ρ : Region} {T : Type} [C T] (xs…) : R (…)`: region parameters first (implicit,
so quantity 0, RD12), then type parameters, then instance arguments, then values.
`struct S where f : T` ↦ `structure S where f : ⟦T⟧` (fields at ω, RD2).
`enum E where | c (x : T)` ↦ `inductive E where | c (x : ⟦T⟧)`. Names are unchanged
(no `Rs.` namespace yet: Wiz has no namespaces). (01, 04, 05, 07)

**L2. Results and panics (RD7).** Every lowered function returns `R _`, even when it
can't panic (a later optimisation may drop it, R7c). Every panic — overflow,
out-of-bounds, `unwrap` on `none`, division by zero, `panic!` — is `.err (…)` with an
`Error` constructor. A function whose Rust type is `Result T E` returns
`R (Except E T)`: user errors are values, panics are not. (06)

**L3. Arguments.** An owned or `Copy` argument is a plain argument. `&'a T` is
`Shr ρ ⟦T⟧` (the value, shared). `&'a mut T` is a plain `⟦T⟧` argument that is **handed
back**: the result type is `R (Ret × T₁ × … × Tₖ)` with one component per `&mut`
argument, in order (a Unit `Ret` is kept). (01, 02, 07, 09)

**L4. Returned borrows (Aeneas backward functions, RD11).** A function returning
`&'a mut A` borrowed from its `&'a mut S` argument returns `R (Mut ρ A S)`, where
`Mut ρ A S = Store A S = A × (A → S)`: the borrowed value and the backward function
that rebuilds the lender from the borrow's final value. The lender is *not* also handed
back (it is inside the closure). `&mut` arguments in other regions are handed back as in
L3. `Option (&'a mut A)` returns `R (MutOpt ρ A S)` = `R (Affine A S)` (L12). (03, 08)

**L5. Sequencing.** A call or primitive that may fail is a direct `match`:
`match ⟦e⟧ with | .ok x => ⟦rest⟧ | .err e => .err e` — never `Monad.bind`, never a
closure around an owner (plan §5.1 req. 2). Pure steps are `let`. Each nested match
is laid out with its alternatives on their own lines; a non-final nested match is
parenthesised. (all)

**L6. Mutable locals are SSA.** `let mut x := e` is `let x := e`; each assignment
`x := e` rebinds `x` (`let x := …`), shadowing the old one. After a call that hands back
`&mut` arguments, each is rebound from the result tuple (`let v := r.2`). (all)

**L7. Joins.** An `if`/`match` whose branches assign variables that are live afterwards
returns those variables from each branch (as a tuple) and the continuation rebinds them.
When the continuation is short, it is duplicated into the branches instead (05).

**L8. Loops (RD8).**
* `for i in a..b do body` ↦ a function `f.loopN` structural on the number of iterations
  left, taking the counter and the live mutable variables, returning the variables.
  The increment can't overflow (`i < b`), so it is unchecked (02).
* `while`/`while let`/`loop` ↦ `partial def f.loopN (params…) (live vars…) : R (Flow (vars) (Ret × &mut args))`,
  tail recursive. Normal exit (`brk`) returns the loop's live variables; a `return e`
  inside the loop ends every borrow and exits with `.ret (e, &mut args)`, which the
  caller returns as is (05, 06, 09). Loop invariants (parameters not assigned in the
  loop) are passed unchanged. `break` = `brk`; `continue` = the recursive call.
* `decreases m` stays a comment until well-founded recursion exists (decreases-loops);
  then `partial` goes and `termination_by` comes in.

**L9. `?`.** On `Option`/`Result` values, a direct match: `.some x`/`.ok x` continues,
`.none`/`.error e` returns `.ok (.none)`/`.ok (.error (From.from e))` from the function —
`.ok` because a returned error is not a panic. Inside a loop it exits with `Flow.ret`. (06)

**L10. Places and place functions.** A place is a path `x.f.g`, `*r`, `x[i]`, a variant
payload. For each struct field the front end emits a field lens `S.fL : Lens S F` with
its laws (`S.fL_lawful : Lens.Lawful S.fL`, by `rfl`) and the independence of distinct
fields (`Lens.Indep`, by `rfl`) — generated, at quantity 0 (07). A function whose body
is a place expression (after NLL) is a *place function*: its lowering is a (partial)
lens, and the front end emits its lawfulness (03: `get_mut.lawful`, from library lemmas
`List.atL_lawful`, `Vec.indexMut_lawful`). Indexing `v[i]` for writing is
`Vec.indexMut i : PLens (Vec A) A` (in place natively via takeAt/fillAt); for reading it
is `Vec.index v i : R A` (shared).

**L11. Borrows of statically known places are aliases.** `let h := &mut s.hits` where
the place is known at compile time does not create a value: the struct is unpacked
**once, before any new field value is computed** (tuple pattern `(h, m, _)`, plan §5.1
req. 1), the fields live as SSA locals while borrowed, and the struct is rebuilt with
its constructor when the last borrow of it ends — in the same block, so Perceus reuses
the cell (`#ir record` shows `reuse … ctor`). Calling a function on such borrows passes
the locals and rebinds them from the handed-back tuple. The optic form
(`zoom S.fL f s`, `zoom (Lens.pair S.aL S.bL) g s` for two disjoint borrows) is
equivalent and is what the front end uses when the place is *not* a direct field of a
local (e.g. through a returned borrow); lowered/07 shows both. (07)

**L12. `Option (&mut A)`.** Returned as `Affine A S`; the caller matches
`.some x k` (a borrow; `k` ends it) or `.none s` (the lender, unchanged). `if let .some x
:= first_mut v` is that match (08).

**L13. Boxes and moves.** `Box T` is `T` (the heap is implicit). Moving out of a box or
a local is just using the variable; a moved variable is never used again (the borrow
checker guarantees it), so Perceus frees or reuses it at that point. Matching an owned
enum moves its fields out; the matched cell is reused by a constructor built in the same
block (04: `#ir reverse.loop0` shows `reuse … ctor 1`).

**L14. `mem.*`.** `mem.swap x y` ↦ exchange the two values (01). `mem.take l` ↦ `let old
:= l; let l := Default` (04). `mem.replace l v` ↦ `let old := l; let l := v`.

**L15. Matching on a borrow.** `match t with | .node key left right => …` with
`t : &mut Tree` binds the fields as reborrows: `left`/`right : &mut Tree`, `key : &U64`.
Lowered: match the value, recurse on/assign the field variables, rebuild the constructor
in each branch and hand the whole back (05, `insert`). A `&T` scrutinee binds fields by
value (shared).

**L16. A borrow that moves (cursor loops, R6c).** `cur := left` inside a loop, where
`cur : &'a mut Tree`, composes the cursor's backward function with the child's:
`cur := Store.comp cur (fun _ => (left, fun l => Tree.node key l right))`; the cursor
starts as `Lens.id t`, and when the loop ends, `*cur := e; t := Store.extract …` puts the
whole tree back (05, `insert_loop`). The defunctionalised alternative (a zipper `Path`
whose frames reuse the nodes, `plug` as the backward function) is what the front end
should emit for performance (05, `insert_zip`), proven equal to the closure form later.

**L17. Regions at call sites.** Region arguments are phantom, so they can't be inferred:
calls pass them explicitly (`@f ρ …`). A region of a local borrow is passed as
`Region.static` today (wrong in spirit; region-indices wants local regions). Recursive
calls omit them (they're parameters passed unchanged).

**L18. Specs (RD13, RD11).** `requires P ensures Q` ↦ `def f.spec (args) : Prop :=
P → Result.All (fun r => Q[result := …, old(x) := x, final(x) := …]) (f args)`; for a
returned borrow `r : Mut ρ A S`, `*result` is `r.1`, `final(result)` is a universally
quantified `fin`, and `final(v)` is `r.2 fin` (03: `get_mut.spec`, proved as
`get_mut.spec_holds`). No prophecy axioms.

**L19. Interop (RD16).** Wiz calls lowered functions as they are (`R`, handed-back
tuples, backward closures); `Result.map`, `Result.show`, `Store.extract`, `Affine.over`
are the helpers (`#eval`s at the end of each lowered file).

## 3. What the lowering guarantees about in-place execution (informal)

At every update the updated value has rc 1 when the Rust program is accepted: `&mut`
arguments are moved into the callee and back (02), struct updates unpack first (07),
enum cells matched and rebuilt in one block are reused (04, 05), element borrows go
through take/fill (natively; the model copies). The dynamic check is `--check-unique`
(R7, not yet built).
