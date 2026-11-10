# wiz-rs drafts: what checks, what doesn't, and why

Branches `agent/rust-drafts`, `agent/rust-regions` (regions). Check everything that
should check, and that the rejected programs fail, with `sh drafts/rust/check.sh` (from
the worktree root, after `lake build`); the libraries' tests are `lake test -- optic`
and `lake test -- regions`.

## Checks today

| file | contents | evidence |
|---|---|---|
| `lib/Optic.wiz` | `Error`, `Result` (+ `bind`, `map`, `Monad`, `All`, `Holds`); `Store` (`comp`, `compP`, `underR`, `extract`, `put`); `Lens`, `PLens`, `ALens`; `Lens.comp`, `PLens.comp`, `Lens.toP`; `zoom`, `zoomP`; `Affine` (`comp`, `over`, `extract`); `TraverseMut` + `List` instance; laws `GetPut`/`PutGet`/`PutPut`/`Lawful` (total and partial), `Lens.Indep`, `Lens.pair` | `lake test -- optic` (4 cases) |
| | **proofs:** structure-field lenses lawful and independent (`rfl`); head of a list (`List.headL`) and **index of a list (`List.atL i`) lawful partial lenses** (all three laws, by induction on the index through generic `Store.underR_*` lemmas); **composition of lawful lenses is lawful** (`Lens.comp_lawful`); `Lens.pair_getPut`; `Store.final` (the `final(r)` desugaring equation) | kernel-checked; a negative test shows an unlawful lens's GetPut is rejected |
| `lib/Region.wiz` | `Region`, `Outlives` (opaque; `refl`/`trans`/`static`); handles as structures `Shr`, `Uniq`, `Mut`, `MutOpt`, `Lent` (the region is part of the type and inferred; constructors private to the module, so handles can't be forged); borrow scopes `Region.scope`, `Shr.borrow`, `Uniq.borrow`, `Uniq.reborrow`, `Uniq.share`, `Uniq.zoom`, `Uniq.both`; `Shr.weaken`; `Mut.ofLens`/`ofPLens`/`whole`/`get`/`set`/`close`/`release`/`comp` | `lake test -- regions` (8 cases: distinct regions, inference, scopes run, outlives, E0515, E0597, E0499/E0502, forging) |
| `drafts/rust/lib/RsCore.wiz` | `Flow`; Nat-backed `U64` (checked `add`/`sub`/`mul`, `checkedAdd`, `midpoint`); List-backed `Vec` (`push` on a `Uniq`, `len` on a `Shr`, `index`, `indexMut` as a lawful `PLens` with proof, `getMut` as `MutOpt`) | `check.sh` |
| `drafts/rust/lowered/01_swap.wiz` | `swap` through two `&mut` (`Uniq ρ₁`, `Uniq ρ₂`), `mem.swap`; nested borrow scopes at the call site | `#eval` .ok (2, 1) |
| `…/02_push.wiz` | `push_twice (v : &mut Vec U64)`, `for` loop as structural recursion | 10 elements |
| `…/03_get_mut.wiz` | returned `&'a mut` as `Mut ρ U64 (Vec U64)`, called in a reborrow scope; generated lawfulness; the `ensures … final(v) = old(v).set i final(result)` spec **stated and proved** | `.ok [1,12,3]`, `.err .outOfBounds` |
| `…/04_reverse.wiz` | in-place reversal with `while let` (partial def), `mem.take` | `#ir`: `reuse … ctor` |
| `…/05_bst.wiz` | BST insert: recursive `&mut` (field reborrows in scopes; now `partial`, reborrow-recursion), cursor loop as a `Mut.comp` chain, and as a zipper | three agree |
| `…/06_count.wiz` | `while` + `?` on a user `Result` (`R (Except E T)`) + `Flow.ret` | ok and returned-error cases |
| `…/07_disjoint.wiz` | two disjoint `&mut` field borrows: place aliases (unpack/rebuild in a reborrow scope) and the optic form (`Uniq.zoom`, `Lens.pair`, `Uniq.both`), generated field lenses + laws + independence | both `.ok (12, 4)` |
| `…/08_first_mut.wiz` | `Option (&mut U64)` as `MutOpt` | some / none cases |
| `…/09_bsearch.wiz` | `&'a Vec U64` as `Shr ρ`, `while` with early `return` | found / not found |
| `…/10_regions.wiz` | `'a : 'b` bounds as erased `Outlives` arguments (`longest`, `remember` storing a `&'a` into a `&'b` slot), nested scopes handing out evidence | `.ok 8` |
| `drafts/rust/rejected/*.wiz` | E0515 (return a local's borrow), E0597 (borrow outlives its scope; short reference stored into a long slot), E0499 (two `&mut`), E0502 (lender used while borrowed), missing `'a : 'b`; a forged handle (`forge_handle`: the handles' constructors are private to `lib/Region.wiz`, docs/stages/13-language.md, 13b) | each rejected with a type mismatch, the forgery as private (`check.sh`) |

## Doesn't check (wishful), and why

| file / feature | missing | wishful entry |
|---|---|---|
| every `drafts/rust/surface/*.wiz` | the `rust … end` command macro and grammar (the front end itself), with positions, coded diagnostics, environment queries | `command-proc-macros` (+ existing `quotation-splices`) |
| `{'a}`, `{'a : 'b}`, `&'a mut T` in the surface | region tokens (local regions and inference are done: scopes and phantom parameters) | `region-indices` |
| structural recursion through a field reborrow (05 `insert` is `partial`) | the termination checker seeing a recursive call on a scope's handle of a pattern variable | `reborrow-recursion` |
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

7. **Escapes reported as "rigid mismatch".** When a scope's body returns a handle of the
   scope's region, the error is sometimes "type mismatch … (rigid mismatch)" between two
   metavariables (`Result (?m1 ρ x)` vs `Result (?m5 ρ x ρy hy y)`), not "a variable
   escapes the scope of the hole being solved" (which it does say when the type is
   already concrete). Both are correct rejections; the message should name the escaping
   region. `drafts/rust/rejected/` shows each.
8. **Unannotated scope lambdas** (`fun ρ h v r => …`) check when the expected type is a Π
   with quantity-0 binders: no annotations needed, but the scope's `B` is solved from
   the body, so errors point into it.

## Measurements wanted (not done: no timing claims)

* Allocation/reuse counts (`#run` heap or a future `--stats`) for lowered/04 (expect 0
  allocations in `reverse.loop0`), 05 (closure chain vs zipper), 07 (struct cell reuse).
* The handles are one-field structures, boxed at run time (`#ir`: `proj 0 x1`), so every
  `Uniq`/`Shr`/`Mut` costs a cell and every `Uniq.set` a reuse at best; and the scopes are
  closures (`Uniq.borrow σ s (fun …)`), unless inlined. Wanted: counts before/after this
  change for 01, 02, 07, and either newtype unboxing of one-field structures or inlining
  of the scope combinators.
* Whether the closure form of `get_mut` (03) reuses the vector when compiled; it can't
  natively until `Vec` is native (implemented-by).
