# wiz-rs drafts: what checks, what doesn't, and why

Branch `agent/rust-drafts`. Check everything that should check with
`sh drafts/rust/check.sh` (from the worktree root, after `lake build`); the library's
tests are `lake test -- optic`.

## Checks today

| file | contents | evidence |
|---|---|---|
| `lib/Optic.wiz` | `Error`, `Result` (+ `bind`, `map`, `Monad`, `All`, `Holds`); `Store` (`comp`, `compP`, `underR`, `extract`, `put`); `Lens`, `PLens`, `ALens`; `Lens.comp`, `PLens.comp`, `Lens.toP`; `zoom`, `zoomP`; `Affine` (`comp`, `over`, `extract`); `TraverseMut` + `List` instance; laws `GetPut`/`PutGet`/`PutPut`/`Lawful` (total and partial), `Lens.Indep`, `Lens.pair` | `lake test -- optic` (4 cases) |
| | **proofs:** structure-field lenses lawful and independent (`rfl`); head of a list (`List.headL`) and **index of a list (`List.atL i`) lawful partial lenses** (all three laws, by induction on the index through generic `Store.underR_*` lemmas); **composition of lawful lenses is lawful** (`Lens.comp_lawful`); `Lens.pair_getPut`; `Store.final` (the `final(r)` desugaring equation) | kernel-checked; a negative test shows an unlawful lens's GetPut is rejected |
| `drafts/rust/lib/RsCore.wiz` | `Region`, `Shr`, `Mut`, `MutOpt`, `Outlives`; `Flow`; Nat-backed `U64` (checked `add`/`sub`/`mul`, `checkedAdd`, `midpoint`); List-backed `Vec` (`push`, `len`, `index`, `indexMut` as a lawful `PLens` with proof, `getMut` as `Affine`) | `check.sh` |
| `drafts/rust/lowered/01_swap.wiz` | `swap` through two `&mut`, `mem.swap` | `#eval` .ok (2, 1) |
| `…/02_push.wiz` | `push_twice (v : &mut Vec U64)`, `for` loop as structural recursion | 10 elements |
| `…/03_get_mut.wiz` | returned `&'a mut` as `Mut ρ U64 (Vec U64)`; generated lawfulness; the `ensures … final(v) = old(v).set i final(result)` spec **stated and proved** | `.ok [1,12,3]`, `.err .outOfBounds` |
| `…/04_reverse.wiz` | in-place reversal with `while let` (partial def), `mem.take` | `#ir`: `reuse … ctor` |
| `…/05_bst.wiz` | BST insert: recursive `&mut`, cursor loop as `Store.comp` chain, and as a zipper | three agree |
| `…/06_count.wiz` | `while` + `?` on a user `Result` (`R (Except E T)`) + `Flow.ret` | ok and returned-error cases |
| `…/07_disjoint.wiz` | two disjoint `&mut` field borrows: place aliases (unpack/rebuild) and the optic form (`zoom`, `Lens.pair`), generated field lenses + laws + independence | both `.ok (12, 4)`; `#ir`: reuse |
| `…/08_first_mut.wiz` | `Option (&mut U64)` as `Affine` | some / none cases |
| `…/09_bsearch.wiz` | `&'a Vec U64` as `Shr ρ`, `while` with early `return` | found / not found |

## Doesn't check (wishful), and why

| file / feature | missing | wishful entry |
|---|---|---|
| every `drafts/rust/surface/*.wiz` | the `rust … end` command macro and grammar (the front end itself), with positions, coded diagnostics, environment queries | `command-proc-macros` (+ existing `quotation-splices`) |
| `{'a}`, `&'a mut T` in the surface; local regions in lowered code | region tokens; a fresh erased region for local borrows; inference of phantom region args | `region-indices` |
| `requires`/`ensures`/`invariant` | spec clauses → quantity-0 spec defs | `spec-clauses` |
| `final(x)`, `old(x)` | desugaring over the backward function | `final-specs` |
| `decreases` on loops | well-founded recursion; loops stay `partial def` (unverifiable) | `decreases-loops` |
| `let i : U64 := 0` | numerals at machine-int types | `machine-int-literals` |
| `∃`, `∧`, `¬`, `∈` in laws/specs (`drafts/rust/Optic.wiz` §1, surface 09) | Prop connectives | `prop-connectives` |
| `Lens.pair_putPut` (`drafts/rust/Optic.wiz` §2; `pair_putGet` is in lib/Optic.wiz since `castRefl`) | the unifier comparing an equation with its computed form | `unify-computed-equations` |
| native `Vec` with `takeAt`/`fillAt` (RsCore uses a List model) | `implemented_by` | `implemented-by` |
| backward functions that reuse cells without inlining (`drafts/rust/Optic.wiz` §7) | constructor contexts | `constructor-contexts` |
| `transp` with a Prop motive using its variable | quantity-0 variables used in types count as ω | `erased-use-in-types` (worked around in `Optic.subst`) |
| `match s with \| .mk h m` on a structure | constructor patterns on structures (tuple patterns work) | `structure-patterns` (low priority) |
| `deriving instance Lenses for S` (`drafts/rust/Optic.wiz` §6) | command macros over reflected structures (agent/deriving has the base) | `command-proc-macros` |
| `RStore` refined backward functions, `FunList` traversal spec (`drafts/rust/Optic.wiz` §4–5) | front-end proof obligations at borrow end; the `Vec` model | `spec-clauses`, `implemented-by` |

## Elaborator issues found (worked around; not wishful features, reported for fixing)

1. **Implicit arguments in a parameter type of an equation-style definition stay
   metavariables.** `def f … (hC : (x : A) → Store.underR k (m x) = C (k x)) : (r : …) → …
   | .ok st, h => … | .err e, h => ()` → "kernel does not accept metavariables (?m1)";
   writing `@Store.underR A B S k (m x)` fixes it (lib/Optic.wiz `underR_pg`/`_pp`).
   The same statement checks as an `axiom` or as a non-matching `def`, so it's the match
   compiler's reverted parameters.
2. **`@f` on the recursive call of an equation-style definition** is "unknown identifier"
   (lowered/05: recursive calls must omit the region argument, which works because it is
   a parameter before the colon).
3. **`.c` constructors inside tuple components** (`.ok (.nil, st)`, `.ok (.true, v)`) get
   no expected type ("no elaborator for syntax kind term.dotIdent"); write `List.nil`,
   `Bool.true`.
4. **Generalised field notation doesn't see through `def`-aliases** (`st.put fin` for
   `st : Store A S` fails; `Store.put st fin` works) — expected, since `Store` is a
   `def`, but it makes the library less pleasant (nominal `structure Store` would fix it
   at the cost of the pair patterns).
5. **Unifier vs computed equations** (see `unify-computed-equations`): every congruence
   in a proof needs all implicit arguments explicit.
6. `match` on a non-variable discriminant doesn't generalise hypotheses that mention it
   (`match List.atL i xs, ih with …`); worked around by stating lemmas over an arbitrary
   `r` and instantiating them (the `Store.underR_*` lemmas). A `match h : e with` form
   would make this direct.

## Measurements wanted (not done: no timing claims)

* Allocation/reuse counts (`#run` heap or a future `--stats`) for lowered/04 (expect 0
  allocations in `reverse.loop0`), 05 (closure chain vs zipper), 07 (struct cell reuse).
* Whether the closure form of `get_mut` (03) reuses the vector when compiled; it can't
  natively until `Vec` is native (implemented-by).
