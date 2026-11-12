# Soundness and metatheory status

This page says what is known about whether Wiz's core is **consistent** (no closed proof
of `False`), whether its type checking **terminates**, and whether its **quantities**
mean what they claim. It is meant to be honest first: if something is not proved, it says
so. The calculus itself is specified in [CoreSpec.md](CoreSpec.md); section numbers
written "§n" refer to it.

The state described here is `master` at commit `9717950` (2026-11-09), plus
the results of the probes listed in the "Probes" section.

## Status values

| value | meaning |
|---|---|
| **published** | a published paper gives a model or a proof that covers it (cited) |
| **folklore** | widely believed and argued informally; no complete write-up that covers Wiz's version is known to us |
| **conjecture** | argued in the Wiz notes or here, not reviewed by an expert, no proof |
| **open issue** | a known problem: a counterexample or a confirmed gap, not yet fixed |
| **fixed** | a known problem that was fixed; the commit and the regression tests are given |

"Unverified" marks a citation or a claim we did not check against its source.

## Summary

* **Nothing about Wiz as a whole is proved.** There is no model of the full calculus and
  no mechanised proof. The individual ingredients (QTT, observational equality with an
  impredicative `Prop`, sized types, descriptions) each have published metatheory for
  *their own* systems. Wiz's combination of them has **no published model**.
* **Regularity is off (D1).** Definitional regularity together with an impredicative
  `Prop` and proof-irrelevant equality is the Abel–Coquand setting [AC20], and the D1
  experiment produced a closed program on which both kernels looped. Decision D1 (a):
  regularity is off in both kernels, `cast` computes on data constructor by constructor,
  and the program now checks. One departure from the published "off" theory remains, a
  **conjecture**: regularity is kept at *inert* (first-order data) types (D1 below; now argued relative to the system without regularity, with one incompleteness found).
* **The kernels never evaluate a proof (P2, closed up to two stated gaps).** Both
  kernels suspend the proofs of `cast` and `transp`, a cast between propositions is
  stuck, and every other proof in an evaluated position must carry a **proof marker**
  that the kernel verifies and requires (CoreSpec §8.6a). That is the algorithm the
  published decidability results are about ([PT23], [PLT25]). Open: the elaborator's own
  evaluation of terms it has not marked yet (bounded where it reads proofs back, by a step
  budget; P2 below). (U5, a `Π`/`Σ` without its sort, is closed by **mandatory sorts**:
  every `Π`/`Σ` carries its two components' sorts and every `ULift` its content's, and the
  kernel checks each, CoreSpec §2.)
* **Four proofs of `False` in the kernel have been found and fixed** (propositions
  compared by shape; `∞ < ∞`; quantities that differ only by a variable, F6; a syntactic
  comparison that missed a variable, F7), each with regression tests. A failure of
  subject reduction for small description fields (Q4) is fixed too (F5, `ULift`).
* **Three proofs of `False` were found while writing this page, and confirmed by
  running them** (see "Open issues" and "Probes"):
  * **O1** (fixed in `c079d1b`): the self-hosted kernel reduced `Size ≡ Size` to
    `False`, so `reflTy Size : False` there (the Lean kernel was not affected);
  * **O2** (fixed, F3, PR #5): a `partial def` at an empty instance of an indexed
    family passed the elaborator's inhabitedness check, and the kernel took it as an
    axiom (`boom : False`, no axioms written);
  * **O3** (fixed, F4, PR #5): a user's `builtin nat.add := K` with a definition that
    disagrees with native addition proved `False`.

  O2 and O3 were not bugs in the kernel's rules: in both, the kernel accepted a
  declaration on trust (an axiom the elaborator vouched for; an unchecked registration).
  Now a partial definition needs a witness the kernel checks, and a registration outside
  the toolchain's library is an axiom that `#print axioms` reports. Several smaller gaps
  are listed too.

---

## 1. Ingredients

| ingredient | status | source and notes |
|---|---|---|
| Π, λ, application, `let`, Σ with η, `Unit` with η | **published** | Martin-Löf type theory [ML84]; η for Σ and Unit with type-directed conversion is standard (unverified which paper first). |
| Universes `Sort l`, `imax`, impredicative `Prop`, non-cumulative, universe-polymorphic declarations | **published** for CIC-like systems; **folklore** for Wiz's exact algorithm | Lean 4's universe design; Wiz's level normaliser (§4) is sound by construction (it case-splits) and incomplete for `imax`, as in Lean (unverified against Lean's source). |
| Definitional proof irrelevance for `Prop` | **published** | [PT22], [PT23] (TTobs, CCobs); Gilbert et al. POPL 2019 (unverified). Wiz has no inductive propositions, so the Lean 4 `Acc` problem does not arise. |
| Observational equality: `eq` computing by type, `cast`, `transp`, funext, propext | **published** | [PT22] (predicative TTobs), [PT23] (impredicative CCobs: decidability of conversion). Earlier: [AMS07]. |
| Propositions compared by equivalence inside type equality (§8.3) | **conjecture** | This is how TTobs and CCobs treat propositions (rule Eq-Ω: `A ∼ B ⇒ (A → B) ∧ (B → A)`; checked in [PT22] §2.3 and [PT23] Fig. 4). Wiz's version depends on **sort annotations** that the kernel checks; that mechanism is Wiz's own. |
| Quantities in type equality (`(1 x : A) → B ≢ (ω x : A) → B`) | **conjecture** | Not in any OTT paper we know. It is consistent with a model where quantities are part of a type's code. |
| Regularity `cast A A e t ≡ t` | **off** by default (D1); kept at inert types: **conjecture** (argued relative to the regularity-off system; the rule is InReg_conv, [PLT25]'s Cast-Refl restricted to inert types and decided by the conversion checker, with ground equality as the evaluator's fast path, D1); propositionally, the axiom `castRefl`: **folklore** (setoid model) | [AC20]: with impredicative `Prop` and irrelevant equality, full regularity breaks normalisation *of proofs*. TTobs and CCobs do not have definitional regularity; they have the proof term `castrefl`, which is Wiz's `castRefl` ([PT22] §2.2, [PT23] §2.2; checked). CICobs [PLT25] has definitional regularity at **all** types (rule Cast-Refl, side condition by conversion) and proves conversion decidable for a fragment, with an algorithm that never reduces proofs. So regularity at inert types (CoreSpec §8.4) is a special case of a published rule; what is Wiz's own is the restriction, which a proof-reducing evaluator needs. See D1 and `/workspace/wiz-notes/plt-vs-inert.md`. `--regularity full` restores the old rule for experiments. |
| Enumerations, `ecase`, equality of tags | **folklore** | Standard finite types. Labels are ignored (`Enum [a,b] ≡ Enum [c,d]`), which is harmless: a model can interpret `Enum` by its size. |
| Descriptions (`ret`, `arg`, `rec`, `hrec`), `Desc.elim`, `μ`, `ind` | **published** for levitated descriptions without quantities [CDMM10]; **conjecture** with quantities and with `Desc` as a primitive | The eliminator `Desc.elim` is large (into any `Sort v`). Field quantities and the quantity-polymorphic `marg` are Wiz's own. Fields live exactly in `Sort (l+1)`; smaller ones are lifted with `ULift` (F5, was Q4). |
| Observational equality at `μ` (`con x = con y ↦ x = y`, by the description) | **conjecture** | Natural, follows the TTobs pattern for inductive types; [PT22] and [PT23] give ℕ equality rules by constructor (Eq-zero, Eq-Suc); CICobs [PLT25 §2.1, §4.1] gives inductive types *no* rule for equality of elements (it is derivable from the eliminator) and a weaker, non-injective equation between instances. Since 4g every `μ ≡ μ` computes by the codes, to `(I, D, i) = (I', D', i')` at `(J : Sort (l+1)) × Desc J × J`, and equality at `Desc` is structural (CoreSpec §8.4b); this is stronger still than CICobs's equation (injective in the index and in the description); see E1. |
| Sized types: `Size`, `∞`, `↑`, `Size<`, subtyping, `sfix`, `scase` | **published** in outline [AVW17]; **conjecture** for Wiz's rules | Wiz's order and the D2 rule are its own (§10.1). Unfolding only on constructors follows Abel's MiniAgda (unverified). |
| Coinduction: `ν`, `out`, `cocon`, `coit`, `scofix` | **folklore** | Sized coinduction is Abel's; Wiz's exact rules have no paper. Equality at `ν` is stuck. |
| QTT usage accounting (the rig, scaling, subusaging) | **published** for Atkey's system [Atkey18] | Wiz differs: quantities are terms with polymorphism (§5.2), branches are joined (§5.3), eliminators scale methods by ω (Q2, fixed), projections only on unrestricted pairs (§7.1; Q1/R1, fixed), "σ = 1 everywhere, then discard" (§5.4). The differences are **conjecture**. |
| Quantity polymorphism (`Qty`, polynomial usages, `≤` by trying every assignment) | **conjecture** | Sound for finite rigs if each assignment is a valid instance (it checks them all). No paper. |
| Numerals and native arithmetic | **folklore**, conditional on correct `builtin` registrations | The Prelude's registrations are trusted (reviewed, §7); any other is an axiom (F4). |
| Glued (lazy) unfolding, `lazyInd` | **folklore** | An implementation technique; it must give the same answers as eager unfolding. Not proved. |

## 2. Interactions

| interaction | status | notes |
|---|---|---|
| QTT + dependent types | **published** [Atkey18] | Wiz's simplified σ-handling: conjecture (§5.4). |
| QTT + observational equality | **conjecture** | No published system combines them. Proofs and types are erased (usage 0), `cast` passes its argument's usage through. Erasure soundness (a 0-quantity value is never needed at run time) is what QTT should give; it is not proved for Wiz. |
| QTT + descriptions | **conjecture** | Fields carry quantities; the payload Σ uses them; methods are scaled. No paper. |
| QTT + sized types + coinduction | **conjecture** | Sizes are erased (always quantity 0). No paper. |
| Observational equality + impredicative `Prop` + regularity | **resolved by D1 (a)**: regularity off; at inert types **conjecture** (argued, see D1) | D1, below. |
| Observational equality + descriptions (`eq` at `μ` and at `Desc`, `cast` between `μ` types) | **conjecture** (model obligation E1) | `cast` between any two `μ` types computes on constructors along the decomposed equation (PT22/CIC-obs style, CoreSpec §8.4, §8.4b). `List A ≡ List B` computes, and gives `A ≡ B`; `UIntN 8 ≡ UIntN 16` is refutable. Makes `μ` injective in its description (Hur's shape, D4): argued in §8.4b. |
| Observational equality + sized types | **conjecture** | Subtyping is not reflected in type equality (`μ^s ≡ μ^t` stuck). |
| Sized types + `∞` | **fixed** (D2) for `∞ < ∞`; **conjecture** otherwise | F2 below. |
| Sort annotations + level polymorphism | **conjecture** | Annotations are checked symbolically (`Level.equiv`), so they stay right under instantiation if `Level.equiv` is sound (it is designed to be). |
| **QTT + OTT + descriptions + sizes + coinduction, all together** | **no published model** | This is Wiz. The STC plan (`/workspace/wiz-notes/stc-plan.md`, M0–M1) proposes a mechanised model of a fragment ("F0") without regularity or with a predicative `Prop`. |

---

## 3. Fixed issues

### F1. Propositions compared by shape gave `False` — **fixed**

* **The bug.** `Eq Prop P Q` computed to `(P → Q) × (Q → P)` (propext), but type equality
  compared a proposition *inside* a type by its shape. `True = (True → True)` is provable
  at `Prop`; carried by `transp` to `(True → Unit) ≡ ((True → True) → Unit)`, whose domain
  equation was `False` by shape. Result: `anyType : (A : Type) → A`. Found by the
  adversarial review (`/workspace/wiz-notes/xtt-cubical-attacks.md`, A0).
* **The fix.** Π and Σ carry their sort; the kernel checks it; type equality and `cast`
  treat two propositions by equivalence, and a proposition is never equal to a
  non-proposition (§8.3, §8.4). Commit **`1b6dc00`** ("Fix a proof of
  False: type equality compares propositions by equivalence"; `cfac255` in the old exercise tree, now `exercises-archive`).
* **Regression tests.**
  * group *observational equality*: "equivalent propositions of different shapes don't
    prove False" (the attack, must fail) and "propositions in a function type's domain
    compare by equivalence" (`#reduce` of the equation);
  * group *selfhost*: "both kernels compare propositions by equivalence (and agree on it
    below)" (Lean kernel verdicts on `MTm.propShapes`);
  * the differential test runs `MTm.propShapes` through both kernels (they are in
    `MTm.samples`).
* **What remains.** A Π/Σ with **no** annotation makes type equality stuck: sound but
  incomplete ("stuck but sound", §5 below).

### F2. `∞ < ∞` (decision D2) — **fixed**

* **The bug.** `t ⇐ Size< s` was checked as `↑t ≤ s`. Since `↑∞ = ∞` and everything is
  `≤ ∞`, this accepted `∞ : Size< ∞`, and `x : Size< ∞` for any `x : Size`. In Agda the
  same rule makes well-founded induction on sizes inconsistent (Agda issue #3026). No
  proof of `False` was built in Wiz (the attack review, D2, could not build one, since
  Wiz has no user-level recursion on `Size`), but the rule was the known-bad one.
* **The fix.** `sizeBelow` (`Conv.lean:143`, `Kernel.wiz:1413`): below `∞` are only
  `↑ᵏ x` for a variable `x : Size< u`. Commit **`fb9074d`** ("Decision D2:
  ∞ is not below itself (both kernels)"; `d521cfa` in `exercises-archive`).
* **Regression tests.**
  * group *sized types*: "∞ is not a size below ∞";
  * group *selfhost*: "∞ is not below itself (and both kernels agree on it below)"
    (`MTm.sizeInf`: 5 rejected, 5 accepted), and `MTm.sizeInf` is in the differential
    samples.
* **Status of sizes otherwise:** conjecture. The atlas still lists `sized-types`,
  `sized-recursion`, `sized-corecursion`, `sh-kernel-sizes` and `sh-kernel-coinduction` as
  "known-issue" for `∞ < ∞`; that is out of date.

### F3. Partial definitions at an empty index gave `False` (was O2) — **fixed**

* **The bug.** `partial def f : T := …` made `f : T` a kernel axiom, guarded only by
  the elaborator's `inhabitedTy`, which looked at the type's *head*: `T.mk : T .t` made
  `T .f` look inhabited, so `partial def bad : T .f := bad` and a `match` gave
  `boom : False` (also `partial def bad : T .t → T .f`).
* **The fix.** A partial definition carries a **witness** (`Decl.witness`), a term of
  its type that the kernel checks (`addPartialDecl`, erased); `addPartialImpl` accepts only
  such declarations, and `inhabitedTy` is gone. The elaborator finds the witness
  (`Elab/Witness.lean`: constructors and constants unified against the goal, so indices
  must match; `fun`, pairs, `Inhabited.default`, …) or the user writes
  `partial (default := w) def …`. Both self-hosted mirrors do the same (`checkPartial` in
  `Kernel.wiz`, `addPartials`/`wit` in `Frontend.wiz`). PR #5 (`agent/trust-gaps`, first
  commit `ebb6a08`).
* **Regression tests.** Group *trust*: the probe and its Π variant are rejected, a wrong
  `default` is rejected, the kernel rejects missing and ill-typed witnesses, inferred and
  written witnesses are accepted, and the self-hosted frontend rejects the probe.

### F4. Unchecked `builtin` registrations gave `False` (was O3) — **fixed**

* **The bug.** `builtin nat.add := K` made `K` compute natively on numerals whatever its
  definition, so a lemma proved by unfolding `K` was refuted by native computation:
  `bad : False`. `builtin nat := E` for an empty `E` and `(0 : E)` crashed `wiz check`
  (a `check`/`infer` loop on numerals).
* **The fix.** Registrations in modules of the toolchain's `lib/` are trusted (reviewed,
  §7). Any other is recorded (`Globals.assumed`), warned about (at an `import` for a
  module), and reported by `#print axioms d`, which lists every axiom `d` depends on.
  Registrations are checked for shape (`nat` an inductive type, each operation a
  definition `N → … → N`), numerals need `nat.zero` and `nat.succ`, and a numeral at a
  type that isn't the registered data type is an error. PR #5 (`agent/trust-gaps`).
* **A hole in that accounting, closed** (soundness audit, T14). A second registration of
  a key was accepted: after `import Prelude`, `builtin nat.add := K` made the Prelude's
  `Nat.add n 1` unfold through `K` on a variable (the kernel finds the definition by key)
  while numerals stayed native, so `boom : False` followed, and `#print axioms boom`
  showed nothing, since `boom` never mentions `K`. Now **a key is registered once and a
  constant has one key**: a second registration is an error at the command, and also when
  a module elaborated on its own is replayed from the cache next to another registration.
  `nat.zero` and `nat.succ` must be constructors of the registered type (numerals unfold
  through them), and a constant registered under a `nat.` key depends on the numerals'
  registrations as a literal does (`P z z` with `nat.pow := P` is the numeral `1` with no
  literal in the term). So with the Prelude imported nothing more can be registered, and
  without it every registration is an axiom of whatever uses its constant or a numeral.
* **A second hole, closed** (icestick-uart P3). "The toolchain's `lib/`" was `lib/`
  relative to the current directory, so an installed toolchain (its library comes as
  `-I share/wiz/lib`) trusted nothing (every registration of the Prelude was reported
  as an axiom), while a `lib/Prelude.wiz` in the current directory replaced the real one
  and was trusted; and the cache key ignored trust, so the two verdicts leaked between
  runs. Now the trusted library is the one next to the binary, searched first, a file
  that would shadow one of its modules is ignored with a warning, and trust is part of
  every module's cache key (stage 22f).
* **Regression tests.** Group *trust*: the probe's warnings and `#print axioms` output, a
  registration in a module from an `-I` directory, the crash and the shape errors, and the
  Prelude's numerals still computing natively with no axioms; the T14 probe and second
  registrations of `nat`, `nat.zero`, `nat.succ` (rejected, also through the cache),
  non-constructors as `nat.zero`/`nat.succ` (rejected).

### F5. Description fields in smaller universes (Q4, decision (a)) — **fixed**

* **The bug.** `arg q S D` accepted `S : Sort k` with `k ≤ l+1`, but `Desc.elim`'s `marg`
  takes `S : Sort (l+1)`, and universes are not cumulative. So `Desc.elim` on a small field
  reduced to an ill-typed term: `getS (arg True (λ _. ret ())) : Type` reduced to
  `True : Prop`. No proof of `False` was known from it. Small fields were common: every
  proof field of a datatype in `Type`, every field `A : Type u` of a type in `Type (max u v)`
  (`Prod.{u,v}`), and the tag of every type above `Type`.
* **The fix** (CoreSpec §4.1, §9.1). A kernel former `ULift.{l} A : Sort l` for `A : Sort k`,
  `k ≤ l`, with `up`/`down`, β and η; equality `a =_{ULift A} b` is `down a =_A down b`
  (`True` for a lifted proposition, whose boxed proofs are all equal by η and proof
  irrelevance), `ULift A ≡ ULift B` is `A ≡ B` (and `ULift` is a former of its own:
  `ULift A ≡ B` is `False` for another former), `cast` goes through `down` (at a level that
  is never `0`; between lifted propositions it is the equivalence, as for any
  propositions). Then `arg` and `hrec` require the field level to be **exactly** `l+1`
  (`Level.equiv` in `Check.lean`; `lvlEquiv` in `Kernel.wiz`), which gives subject
  reduction for `Desc.elim` (CoreSpec §9.1). The elaborator (`Elab/Inductive.lean`,
  `Elab/Recursor.lean`) lifts small fields, small infinitary domains and the tag of a type
  above `Type`, invisibly: constructors take the fields themselves, recursors and patterns
  hand out `down` of them, printing hides `up`/`down`. `ULift` is erased (`#ir` unchanged).
  `Frontend.wiz` builds only `Desc.{0}` descriptions from a surface without `Prop`, so its
  fields are always in `Type` and need no lifting. Branch `agent/q4-lift`.
* **Regression tests.**
  * group *selfhost*: "Q4: a small description field is rejected, a lifted one works (and
    both kernels agree on it below)" (`MTm.smallField`: the old `getS` counterexample and
    its description are rejected; the lifted description, `getS` of it (`ULift True :
    Type`), boxed proofs, η, type equality and casts at `ULift` are accepted); the terms are
    in `MTm.samples`, so the differential test runs them through `Kernel.wiz`;
  * group *inductive*: "Q4: …" cases for a proof field, the fields of `Prod.{u,v}`, a type
    in `Type 1` with an infinitary field over `Type` and with a lifted tag, and `#ir`
    unchanged by lifting.
* **Deriving** (stage 7d, docs/stages/07-type-classes.md). `deriving` used to fail on a
  type with a proof field (it showed, compared and defaulted the proof: a unification
  error at `BEq`, no `Repr`/`Inhabited` of a proposition) and on universe-polymorphic
  types (an `inductive Box.{u} (A : Type u)` without a signature was put in `Type`, so its
  field was lifted to a level below its own and the kernel rejected `Box.desc`; the
  classes and instances were in `Type` only). Now reflection marks proof fields, the
  derivers skip them, the classes take `Type u`, instances have universe parameters, and
  a missing signature is the smallest `Type l` that holds the fields. Derivers see a
  lifted field through `down` (the recursor's method gets the field at its own type).
  Tests: group *deriving*, "deriving with proof fields …", "… universe-polymorphic type
  …", "… a type above Type: lifted fields are seen through down (F5)".
* **What remains.** The subject-reduction argument is on paper (CoreSpec §4.1,
  §9.1), not mechanised; the OTT rules for `ULift` are the standard ones for a one-field
  former and are **conjecture** in Wiz's combination like the rest of §8.

### F6. Quantities that differ only by a variable made two types unequal — **fixed**

* **The bug.** Type equality between two Π (or two Σ) types computed to `False` when the
  binder quantities were different *as polynomials* (`sameQty q q' == some false`). A
  quantity variable `q` and the literal `1` are different polynomials, so
  `((%q x : N) → N) = ((1 x : N) → N)` computed to `False` for a variable `q`, and the
  instance `q := 1` made it provable:

  ```
  def flip {q : Qty} (e : ((%q x : N) → N) = ((1 x : N) → N)) : False := e
  def boom : False := flip (q := 1) rfl
  ```

  A closed proof of `False`, accepted by the Lean kernel. The decision "False" was not
  stable under substitution (a rule fired that a substitution turns into a different
  rule). It was found by the P1 inventory of syntactic side conditions
  (`/workspace/wiz-notes/p1-stable.md`), and independently by the theory agent (the same
  attack at `Unit`). The self-hosted kernel was not affected: its quantities are literals
  only.
* **The fix.** `qtyApart` (`Eval.lean`). The equation is `False` only when both
  quantities are closed (constant polynomials) and differ (`QPoly.equiv`, so the test is
  invariant under conversion). It is the Σ rule when they are equivalent polynomials. In
  every other case it is stuck. Branch `agent/p1-qty`.
* **Regression tests.**
  * group *quantity polymorphism*: "F6: types whose quantities differ only by a variable
    are not unequal" (the attack, the `Unit` variant and a Σ variant, all must fail) and
    "F6: types with two different literal quantities are unequal";
  * group *selfhost*: "F6: literal quantities that differ make types unequal" (Lean kernel
    verdicts on `MTm.qtyApart`), and `MTm.qtyApart` is in the differential samples.

### F7. Syntactic equality missed a variable captured by a native operation — **fixed**

* **The bug.** `Term.mapChildrenM` had no case for `natOp`, so `Term.freeVarsAt` saw no
  variable in the body of a native operation's closure, and `Val.lvlBound` of the partial
  application `Nat.add x` was `0`. `sameVal` then quoted below `x`, where every variable
  truncates to index `0`: `T (Nat.add x)` and `T (Nat.add y)` quoted alike, `sameFamily?`
  took `μ D_x ()` and `μ D_y ()` for one family, and their equation computed to `() = ()`.
  With `T (Nat.add 0)` inhabited and `T (Nat.add 1)` empty, a cast along the instance at
  `0`, `1` was a closed proof of `False` (Prelude only, no axiom). Found by the soundness
  audit (`/workspace/wiz-notes/soundness-audit.md`, S1; the probe is
  `soundness-probes/s1-natop-samefamily.wiz`). The self-hosted kernel was not affected: it
  has no native operations, and its `usesVar` is conservative.
* **The fix.** The `natOp` case in `mapChildrenM` (`Term.lean`). The constructor list of
  `Term` was compared with the traversal's cases: it was the only one missing.
* **Regression tests.** Group *builtins*: "S1: a variable captured by a native operation
  counts in syntactic equality (it proved False)" (three attacks, must fail) and "S1: the
  same family at the same partial application is still one family".
* **What remains.** `quote` still turns a variable at or above its level into index `0`
  silently (truncated subtraction). An explicit failure there would have made this a crash.

### F8. `absurd` on a glued value evaluated to `Sort 0` — **fixed**

* **The bug.** `vAbsurd` matched only a neutral. For `absurd (lem h)` with `lem` a global
  definition the scrutinee is a glued value, the `panic!` branch ran, and Lean's `panic!`
  returns the default value, `Sort 0`. So `def g (h : False) : Type := absurd (lem h)`
  evaluated to `Prop`, and `def u (h : False) : g h := True` was accepted. Reachable only
  under an inconsistent hypothesis, so no closed proof of `False`. `Kernel.wiz` takes the
  weak head normal form first and was not affected (audit, F2).
* **The fix.** `vAbsurd` unfolds glued values first (`Eval.lean`).
* **Regression test.** Group *observational equality*: "F2: absurd on a lemma's result is
  stuck, not Prop".
* **What remains.** Every other `panic!` in `Eval.lean` also returns `Sort 0` and lets the
  check go on. None is known to be reachable from a well-typed term.

### F9. The eliminators did not check the index type's level (audit F3) — **fixed**

* **The gap.** `μ.{l} I D i`, `ν.{l} I D i` and `Desc.{l} I` require `I` in exactly
  `Sort (l+1)`. The five eliminators that take `I` as an argument (`ind`, `sfix`, `scase`,
  `coit`, `scofix`) only required `I` to be a type, in both kernels, and they build the
  types `μ.{l} I D i`, `ν.{l} I D i`, `Desc.{l} I` as values, without the type former's
  rule. So `coit.{0} (Unit.{2}) …` was accepted with the type `ν.{0} (Unit.{2}) D i`,
  which is not a type, and the method of an ill-levelled `ind` bound variables at such a
  type. The surface language can't write this (the elaborator builds every eliminator from
  a type it has checked); a core term can.
* **Not a proof of `False`**, as far as two attempts could tell (the soundness audit's, and
  a second one with the unchecked positions listed,
  `/workspace/wiz-notes/elim-levels.md`). The ill-levelled type exists only as a value:
  every position that takes a type *term* checks it with the type former, a description
  checked against `Desc.{l} I` at such an `I` can't branch (the motive of a `case` would
  have to name `Desc.{l} I`), and its fields are still small. Semantically such a type is
  a small family with a large index, harmless as long as nothing can state its
  injectivity. But "index level ≤ family level" is the side condition for injective type
  formers ([PLT25 §2.3]: without it, Russell's paradox by Hur's argument), and Wiz's `μ`
  equation is injective in the index (in `(I, D, i)` with PR #40), so the kernel should
  not depend on "nobody can write that type down".
* **The fix.** `checkIndexLevel` in both kernels (`Check.lean`, `Kernel.wiz`): the five
  rules have the premise `Γ ⊢ I type@k`, `k ≡ l+1` (CoreSpec §9.3). No other rule had the
  omission: `con`, `cocon`, `out` take their type from the context, `Desc.elim` infers its
  description, `cast`/`transp`/`=` take type terms.
* **The same kind of gap in `transp`** (second audit; fixed with it). `transp A a P p b e`
  only required `A` to be a type, while `eq` and `refl` require a sort that is never
  `Prop`. Its motive type and the type of `e` are equations at `A`, built as values, so
  `transp` was accepted at a proposition, where the `eq` rule rejects those types. Harmless
  (proofs are irrelevant), same defect. Now `isNeverZero` / `lvlNeverZero` in both kernels
  (CoreSpec §8.1). Tests: "transp at a proposition is rejected, at a type accepted" (group
  *check: structural types*), `MTm.transpProp` in the differential samples and its
  Lean-verdict case in *selfhost*.
* **The hint of `μ`/`ν` was evaluated unchecked** (found by the kernel lint; Lean kernel
  only, `Kernel.wiz` has no hints). The `mu`/`nu` rule ignored the hint `(T, us, args)`,
  and `eval` evaluates its arguments, so a raw core term there was run without having
  been checked: every evaluator `panic!` was reachable, a looping hint hung the checker,
  and a constant could be instantiated at too few levels. The values only land in the
  hint, which conversion ignores, so no wrong acceptance is known. Now `checkHint`:
  `T.{us} args` must be well typed if `T` is declared, and each argument must have an
  inferable type otherwise (CoreSpec §9.3). Test: "the hint of μ/ν is checked before it is
  evaluated" (group *check: structural types*). The hint is not display-only: the
  elaborator finds a type's name, constructors and arguments through it.
* **Regression tests.** Group *check: structural types*: three "F3: ind, sfix, scase,
  coit, scofix …" cases (accepted at `Sort (l+1)`; rejected one level too high and one too
  low, with the error text). Group *selfhost*: "F3 (audit): the eliminators check the
  index type's level", and `MTm.elimLevels` (22 terms) is in the differential samples, so
  `Kernel.wiz` must give the same verdicts.

### T1. A recursive definition's compiled code was not checked by the kernel — **fixed** (typing; two disagreements); agreement with the definition is **checked** (branch `agent/impl-derive`)

* **The gap.** A declaration has a `value`, which the kernel checks and unfolds, and may
  have an `impl`, the term that is *compiled* instead (`Decl.impl`; `eraseDecl` takes it
  first). For a structurally recursive definition by equations the elaborator builds
  `impl` by elaborating the clauses a second time, with direct recursion instead of the
  recursor. `addDecl` checked `value` only: nothing type-checked `impl` or compared the
  two, and everything that compiles ran it (`wiz build`/`run` on both backends,
  `#eval`/`#run`, macros, tactics, derivers, and the self-hosted tools as programs).
  Erasure also read the sorts noted on the `Π`s and `Σ`s inside it, which had never
  passed the kernel's `checkSortNote`. Logical soundness was not at risk: the kernel never
  unfolds `impl`. Found by reading the code (agent mem-hunt).
* **A wrong result.** The two elaborations did disagree. The first recognises a
  recursive call `f y` by its syntax and replaces it by the induction hypothesis; the
  second resolved `f` by scope, so a local variable called `f` captured the call:

      def f : Nat → Nat
        | .zero => 0
        | .succ n => (fun (f : Nat → Nat) => f n) (fun x => x + 100)
      def thm : f 3 = 0 := refl 0      -- accepted: the definition recurses
      #eval f 3                         -- printed 102: compiled code called the local

  (the same with `let f := …`). Both terms have the declared type, so no type check
  finds this.
* **The fix.**
  1. *Kernel.* `addDecl` checks `impl` against the declared type, with the definition
     already declared (`checkImpl`, as `addPartialImpl` does for partial definitions):
     typing, quantities, level parameters and sort notes. `attribute [implemented_by g] f`
     stores its constant through the kernel too (`setImpl`). So every term erasure sees
     has been checked, and erasure reads the sort a `Π`/`Σ` carries everywhere (the
     exception it made for these implementations, `sortNotesChecked`, is removed). **A declaration whose implementation fails is rejected**, not
     compiled from its value with a warning: the implementation is the elaborator's own
     output, so a failure is a bug in Wiz, and falling back would hide it behind a
     program that is correct but computes every recursive call through the recursor (a
     change of cost that nobody asked for and no test would notice). The error says that
     the definition itself checks and that the bug is not the user's.
  2. *Elaborator.* In the second elaboration the calls the first one rewrote are marked
     with a macro scope (`markRecCalls`), so they refer to the definition whatever is in
     scope. `f 3` above now runs to `0`.
* **A second wrong result** (agent impl-derive). The second elaboration inferred the
  implicit index of a recursive call from its argument, where the recursor keeps the
  outer index: `def g {ω n : Nat} : V n → Nat | .cons _ xs => n + g xs` proved
  `g v3 = 9` and `#eval g v3` printed `6`; with an erased index the definition was
  rejected instead. Guarded first (PR #98: no `impl` when an index variable escapes into a
  method), then removed with the second elaboration (below).
* **Resolved: agreement is checked.** The second elaboration is gone. The elaborator
  *derives* `impl` from the checked value (`deriveImpl`, `Elab/Command.lean`): the same
  term with `T.casesOn` for `T.rec` and each induction hypothesis replaced by the direct
  call it stands for (`λ rs. f tele (… y …)`; under its index equation for a match with
  index unification; for a field of another sort of a mutual family, whose hypothesis
  only an equation between different indices could unlock, the recursor itself). Nothing
  is read from the source twice. The kernel checks, besides the type (`checkImpl`), that
  it **agrees with the value** (`checkImplAgrees`, `Core/Check.lean`): applied to fresh
  variables both are stuck on the same argument as `ind P M i x …` and `ind P M' i x …`;
  they must be convertible with `M'` replaced by `M`, and for every constructor tag `t`,
  at a fresh index and payload `xs = (t, rest)`, `M j xs H ≡ M' j xs H` with `H` the
  hypotheses `ind` computes (each direct call unfolds once to the stuck `ind` on a field).
  By induction on the scrutinee, compiled code computes what the kernel computes. A
  definition whose index variable escapes into a method gets no `impl` (compiled from its
  value). `#print axioms` lists nothing for compiled equations (it did, as `compiled f`,
  between the two steps).
  * *Code quality.* The derived term passes a call as an argument where a nested split
    reverted the hypothesis, and rebuilds a constructor where a catch-all names the
    scrutinee. Erasure rewrites both before compiling (`Compiler/Push.lean`, from
    `eraseDecl`: calls moved into the inner split's branches, the rebuilt constructor
    replaced by the scrutinee, a closure that only calls the definition inlined); each
    rewrite is checked by the kernel again and dropped if it does not check. Measured on
    lib/, examples/ and the self-hosted compiler: 582 derived implementations, all agree;
    the optimised IR of 560 of 581 definitions is identical to the second elaboration's
    (+0.2% lines overall: unreachable branches of absurd cases in a mutual family);
    allocations equal on a workload of recursive functions (nested splits, indexed,
    infinitary, mutual).
  * *Recognised by syntax, still:* a call `f y` in `f`'s equations is the recursive call;
    a local variable named `f` in scope is now an **error** ("a local variable named f
    shadows the recursive definition f …; rename the local variable").
* **The other places with a second term or a recognition by syntax** (each probed with
  the shadowing example; the kernel's value and the compiled result agree in all):
  sized definitions (one term, `sfix`; the definition's name is an ordinary local);
  copatterns (one term, `coit`; a corecursive call is recognised by syntax, so a
  parameter named like the definition is taken for the call, in the checked term and the
  compiled one alike); partial definitions and `mutual` blocks (a witness and a body:
  unrelated by design, the body is opaque to the kernel and resolves names by scope);
  instance bodies and generated declarations (one term each); `implemented_by` (the
  user's second term: trusted, listed by `#print axioms`).
* **Everything else that is compiled** was checked already: partial definitions' bodies
  (`addPartialImpl`), the terms of `#eval`/`#run` (inferred by the kernel first),
  generated declarations (instances, `deriving`, macros: they are commands, and go
  through `addDecl`), `attribute [inline]` (erases the checked declaration). Declarations
  replayed from the cache are not checked again, by design: an entry is keyed by the
  binary that wrote it, and holds what its kernel accepted, `impl` included. The
  self-hosted frontend elaborates a recursive definition once (recursive calls become
  the hypotheses of `ind`) and its backend compiles that checked value: it has no `impl`.
  The eliminators' own compiled code (`PrimCode.lean`, the runtime's `ind`) is
  hand-written and belongs to the trusted backends (§7).
* **Cost.** One more check per structurally recursive definition. Rough timings of
  `wiz check --no-cache` (best of three, a shared machine): the Prelude 0.27 → 0.31 s,
  `lib/Hoare.wiz` 3.3 → 3.7 s, `lib/Hdl/Core.wiz` 2.0 → 2.3 s, `selfhost/Kernel.wiz`
  5.0 → 5.1 s, all five self-hosted sources together within noise.
* **Regression tests.** Group *trust*: "the kernel checks a definition's implementation
  for the compiler (Decl.impl)" (ill-typed, another type, a wrong sort note, a linear
  variable used twice, an undeclared level parameter, `setImpl`), "recursive definitions:
  the compiled equations are kernel-checked terms", "… a local variable named like the
  definition is an error", "… compiled code keeps an outer index that a method mentions",
  "… compiled equations derived from the value agree with it, with and without moving
  calls out of nested splits", "… the kernel rejects compiled equations that compute
  something else".

---

## 4. Open issues

Ordered by severity. "Reproducer" means a file or term that demonstrates the issue; the
probe outputs are in the "Probes" section.

### O1. `Kernel.wiz` reduced `Size ≡ Size` to `False` — **fixed** (`c079d1b`; was a proof of `False` in the self-hosted kernel)

Fix: `Size` and `Size< s` are no longer `canonical` in `Kernel.wiz`, matching
`Eval.lean`; the equation is stuck in both kernels. Regression tests: "Size = Size is
stuck, not False (and both kernels agree on it below)" (selfhost group) and the
`MTm.sizeEq` samples in the differential test. The original analysis follows.

`Kernel.wiz`'s `canonical` (`Kernel.wiz:552–565`) counts `Size` and `Size< s` as type
formers, and `vEqTypeW` (`Kernel.wiz:937–963`) has no case for two sizes, so
`Size ≡ Size` falls through to "two canonical formers ⇒ `False`". Then
`reflTy Size : False`, and `exfalso M (reflTy Size) : M` for any `M`. The Lean kernel
does not do this (`Size` is not `canonical` in `Eval.lean:572`; the equation is stuck).

* **Reproducer (confirmed)**: `Kernel.wiz` followed by
  `#eval typeOf (.exfalso (.empty 0) (.tyRefl .size))` prints `"Empty0"`: the
  self-hosted kernel accepts `absurd Empty (reflTy Size)`. `typeOf (.tyRefl .size)` and
  `typeOf (.tyRefl (.sizeLt .szInf))` print `"False"`. In the Lean kernel the equation is
  stuck (`#reduce Size = Size` prints `Size = Size`), so the same term is rejected.
* The differential test cannot have caught it: its generator does not build
  `reflTy Size`.
* Fix: add `Size`/`Size<` cases to `vEqTypeW` (stuck, as in Lean, or `True` for
  `Size ≡ Size`), or drop them from `canonical`. Add the term to `MTm.samples`.
* Reach: `Kernel.wiz` is used by the self-hosted frontend; whether the self-hosted
  frontend can produce this term from surface syntax was not checked.

### O2, O3 — **fixed** (F3, F4).

### D1. Regularity + impredicative `Prop` + irrelevant equality: type checking looped — **fixed** by decision D1 (a); regularity at inert types is a **conjecture**

* **Question.** Abel and Coquand [AC20] show that an impredicative `Prop`, a
  proof-irrelevant equality and a cast that reduces whenever the two types are
  definitionally equal (regularity) break normalisation. Wiz had all three.
* **Experiment** (`agent/d1-regularity`, `/workspace/wiz-notes/d1-experiment.md`): their
  literal term does not loop in Wiz (a cast between two visible propositions applies the
  equivalence), but wrapping the proposition in a one-field `μ` type did: regularity
  fired at the box type, and **both kernels looped while type checking a closed,
  axiom-free program**.
* **Decision D1 (a), `agent/d1-off`.** Regularity is off in both kernels
  (`Globals.regularity := .off`, `kernelRegularity := .false`). In its place `cast`
  computes on data (CoreSpec §8.3, §8.4): `μ D i ≡ μ D i'` computed to `i = i'` (since 4g:
  to the equation of the codes, E1) and a
  cast between them casts each field of a constructor along the derived payload equation;
  `Desc` and `ν` likewise; equality at `μ` follows the description constructor by
  constructor, so `succ m = succ n` is `m = n` without a cast. The Abel–Coquand box now
  yields a stuck proof, and the program checks (tests "D1 (Abel–Coquand): the program
  checks …", "… the Wiz kernel checks the program …"). It used to loop with
  `--regularity full --eager-proofs`, when regularity was a rule of evaluation decided
  by comparing the two types as written. Regularity is now decided by conversion only,
  and the program checks in every mode, whichever way the cast's source type is written
  (test "D1 (Abel–Coquand): the cast's source type by name or as inferred …").
* **Departure from the published theory (conjecture).** Regularity is kept at **inert**
  types: `Enum`, `Unit`, Σs of inert types, and `μ` types whose fields are all inert (no
  `Prop` field, function, neutral type or type variable), decided by a syntactic,
  conservative walk (`inertTy` in both kernels). Argument (CoreSpec §8.4): on a neutral
  argument the rule rewrites a neutral to a neutral, so it enables no reduction; on a
  constructor it agrees with the structural rule up to proof irrelevance, and inert
  values contain no λ, so nothing can tell the two apart; conversion is unchanged and
  stays decidable. No normalisation proof covers it. A nested box (a `μ` whose field is
  the Abel–Coquand box) is not inert and checks (test "a box in a box is not inert
  either").

  **Argued, relative to the system without regularity**
  (`/workspace/wiz-notes/inert-regularity.md`, 2026-11-10; it stays a conjecture: the
  argument has not been reviewed). That note corrects the argument above and gives a
  sketch of three properties.
  * **Consistency.** The rule holds in any model where `μ` is an initial algebra and
    `Prop` is proof-irrelevant.
  * **Normalisation of relevant terms.** The rule adds one trivial case to a
    Pujet–Tabareau-style logical relation, provided its side condition is judgmental.
  * **Normalisation of proofs.** Inert types are *rigid*: their reducibility candidate
    does not depend on `Prop` or on type variables. So Girard's candidates argument
    survives a rule that returns its argument unchanged at them, using environments that
    agree at inert types. Abel–Coquand needs a non-rigid type. This property mattered
    while Wiz's evaluator ran proofs (it forced `e` inside `cast`). Since P2 it does not,
    at the positions the syntax marks as proofs (next item), so this third property is
    needed only for the proofs that are still evaluated: those bound by `let` or passed
    as arguments.

  All three assume the same property of the system without regularity, which is itself
  unproved for Wiz. That system already has two identity casts that inspect types: at
  `Enum` on any argument, and at `Sort` (the latter is rule Cast-Univ of [PT22], [PT23]
  and [PLT25]).

  **Related published work** (`/workspace/wiz-notes/plt-vs-inert.md`). CICobs [PLT25] has
  regularity at every type as a *conversion* rule (Cast-Refl: `cast A B e t ≡ t` when
  `A ≡ B`, any `e`), with an impredicative proof-irrelevant sort. Its Agda proof gives
  normalisation of relevant terms and decidability of conversion ([PLT25] Theorem 5.6) for
  a fragment with Π and ℕ and no general inductive types. Two points of method matter
  here:
  * the rule is decided by the conversion checker when it compares neutrals, with a
    conversion test on the cast's two types, never by a syntactic test in the evaluator;
  * proofs are never reduced, which is how Abel–Coquand's term stays harmless.

  So the inert rule is not new, and no counterexample in [AC20], [PT23] or [PLT25]
  applies to it. Their theorem does not cover Wiz: not the kernel as written (it reduces
  proofs), and not descriptions, sizes, `ν`, quantities or `ULift`.

  **Found gap (incompleteness, not unsoundness).** The side condition is syntactic
  (`sameVal`), so algorithmic conversion is not a congruence and is not stable under
  substitution.
  * `cast (Fin (f p)) (Fin (f q)) e k` stays stuck for a variable `k`, although
    `Fin (f p) ≡ Fin (f q)` by irrelevance, while the reflexive cast reduces to `k`.
  * Two stuck casts that are convertible before a substitution stop being convertible
    after one of them becomes syntactically reflexive.

  `sameFamily?` had the same defect; 4g removed it (μ/ν rules are head-directed, E1).
  The fix for InReg is to decide the side condition with
  conversion. Confirmed by a probe (the note, §10): `h p q p` is well typed, but its δβ-reduct is rejected, so subject reduction fails for the algorithmic typing.

  **Fixed (P1, `agent/p1-stable`; `/workspace/wiz-notes/p1-stable.md`).**
  * **The change.** InReg's side condition is ground equality (`groundEqTy`, both
    kernels). It holds for two inert types that are equal and have no free variable in a
    relevant position, so it gives the same answer for convertible types and survives
    substitution. `sameFamily?` is replaced by desc-eq's head-directed rules (PR #40).
    The numeral fast path is subsumed.
  * **The probe as a regression test** (group *observational equality*, "P1: …").
    `h`, `h2` and `h3` check, so the reduct checks iff the term does. `t1` and `t2`
    (InReg at an open index `f p`) are rejected, consistently.
  * **What it costs.** InReg on a variable at an inert type whose index is open
    (`cast (Fin n) (Fin n) e k`). Casts at closed inert types still reduce, and casts of
    constructors at open ones compute structurally. Measured: every test, library file
    and example checks as before, and no cast in `lib/` or `examples/` is decided
    differently from the old rule (the note, §5). The loss shows only on the probe.
  * **Decided by conversion (the user's decision; both kernels; the default).** The rule
    is InReg_conv: `cast A B e t ≡ t` when `A` is inert and `A ≡ B`. It is a rule of
    conversion, [PLT25]'s Cast-Refl restricted to inert types: the conversion checker
    removes a cast that stayed stuck when its two types are convertible (`unCast` in
    `Conv.lean`, `stripCast` in `Kernel.wiz`), on either side, under eliminations too.
    Ground equality stays as the evaluator's fast path, a fragment of the same rule that
    needs no conversion. So the open-index case above is no longer lost: all eight
    probes check (tests "P1: InReg decided by conversion …", and the same as core terms
    on both kernels, "P1: regularity at inert types is decided by conversion, in both
    kernels"). `--inert ground` (`kernelInertConv := .false`) keeps only the fast path.
  * **Syntactic equality is gone from regularity**: `--inert syntactic`, the numeral
    shortcut, `sameVal`, `lvlBound` and `freeVarsAt` are deleted from both kernels, and
    with them the D1 modes `nonprop` and `refl`. `--regularity full` is Cast-Refl at
    every type, in conversion only (an experiment).
  * **Closed by mandatory sorts**: `inertTy` read a `Σ`'s optional sort annotation, so
    conversion with this rule was not transitive at types that differed only in that
    annotation. The sorts are now mandatory and conversion compares them. **Open.** Completeness of "strip when possible, else
    congruence" against [PLT25]'s backtracking algorithm is argued, not proved. The
    theorem behind the rule covers Π, ℕ, ⊥, `Prop`, ∃, not Wiz's data types
    (`/workspace/wiz-notes/conv-regularity.md`).
* **P2: the kernels never evaluate a proof** (CoreSpec §8.6, §8.6a;
  `Globals.lazyProofs`, `kernelLazyProofs`; the user's decisions, 2026-11-10;
  `/workspace/wiz-notes/p2-proofs.md`, `prf-marker.md`).
  * Pujet–Tabareau's and Pujet–Leray–Tabareau's algorithms never reduce a proof, and
    their theorems are about those algorithms. Wiz's kernels ran proofs, so those
    theorems could not cover them even in principle.
  * **Step 1 (PR #61).** The equation of a `cast` and the two proofs of a `transp` are
    suspended, a cast between propositions is stuck, and conversion decides proof
    irrelevance before it unfolds either side.
  * **Step 2, the proof marker.** The evaluator has no types, so a proof bound by `let`,
    passed as an argument or stored in a field was still evaluated. Now there is a term
    former `prf.{l} t` (`l` the sort of `t`'s type), which the evaluator suspends when
    `l` is `0`. The kernel **verifies** it (the level must be the type's sort) and
    **requires** it: outside a proof, a term whose sort may be `0` must be marked or
    neutral-shaped (a variable, a constant or `()` under applications and projections),
    or one of the proofs that are stuck heads (`refl`, `reflTy`, `transp`).
    So every value the evaluator builds at a proposition is a neutral, `()`, or a glued
    constant that unfolds to one, and the kernel never does a β, projection or ι step
    inside a proof. A term that would make it do so is a kernel error ("unmarked proof").
    The elaborator's marking pass writes the markers (`Wiz/Elab/Mark.lean`; `markCheck`
    in `Kernel.wiz` for the self-hosted frontend); it is untrusted.
  * **The marking pass is outside the kernel and may panic on ill-typed input.** It
    checks nothing and evaluates the term as it goes, so every caller must give it
    elaborated terms only (the elaborator makes the same assumption of its own terms).
    Its callers: a declaration the kernel has answered "unmarked proof" to, and a
    theorem, on their way to the kernel (`withMarksOnDemand`: `addDeclSorted`, the two
    partial-definition paths), `#reduce`, and the kernel entries of `Frontend.wiz`. A
    wrong elaborator output can therefore show as a panic in the pass, which ends
    `wiz check`, where it used to be a kernel error message.
  * **Inside a marked proof too** (found by audit-2 on the first version: a `let` inside a
    proof evaluated its value to bind it, and a tower of exponentials in `Prop` hung the
    checker). The mode of a subterm is decided by its type (a relevant subterm of a proof
    is checked in relevant mode again), and inside a proof the checker binds a proof
    suspended (test "P2 (I-1): …", heights 3, 4 and 6 on both kernels). The elaborator's
    `let` does the same.
  * **Level-generic terms.** `(a : A)` with `A : Sort u` is a proof at the instance
    `u := 0`. The marker carries the level, so such a term is marked once, at `u`, and is
    suspended exactly at the instances where it is a proof (tests "P2 (R1): …").
  * Effect on D1: the `let`-encoded Abel–Coquand term used to make `Kernel.wiz` loop with
    regularity on (its proofs are `let`-bound). Marked, it checks in both kernels, with
    `kernelRegularity := .true` and `--regularity full` too (test "D1 (Abel–Coquand): both
    kernels check the let-encoded program, with regularity on too"). Unmarked, both
    kernels reject it.
  * **What [PLT25] proves** (Theorem 5.6): decidability of conversion with full
    regularity, for the fragment with Π, ℕ, ⊥, `Ω`, a proof-irrelevant ∃, the
    observational equality and `cast`, at two universe levels, mechanised in Agda. It
    does not cover general inductive types, and so not Wiz's descriptions, `μ`/`ν`,
    sizes, quantities or `ULift`. Wiz's statement stays "the published algorithm,
    extended; unproved for the extension".
  * **Gap 1, sorts that are not written (U5): closed by mandatory sorts**
    (`wiz-notes/mandatory-sorts.md`). Every `Π`/`Σ` carries its components' sorts
    `⟨dom, cod⟩` (`BinderSorts`; `Kernel.wiz`: `pi q i j`, `sigma q i j`), the kernel's own
    templates included, and each is checked against the inferred sort of its own
    component; `ULift` carries its content's sort. The elaborator writes what it knows and
    one total pass fills the rest (`Decl.withSorts`, inside proofs too); a hole that reaches
    the kernel is rejected. Next: relevance marks on binders (`prf-marker.md` §8).
  * **U5b (found by the property harness, fixed).** `cast` at a `Π`/`Σ` whose sort is not
    known (no annotation, or a level with parameters) used to compute by the `Π`/`Σ` rule,
    projecting a proof `e` whose own type, the equation between the two types, is stuck
    there and is no pair: the result was a term the kernel rejects, and at the level
    instance `0` evaluation did not commute with instantiation. Now the cast is stuck
    exactly when the equation is, in both kernels (test "U5b: …"); `Kernel.wiz`'s payload
    types and the `hrec` field's `Π` carry their sorts so that casts on data compute as
    before. No verdict in `lib/`, `examples/` or `selfhost/` changes. With mandatory sorts
    "not known" means only "depends on a level parameter".
  * **D2 (found by the meta-review): closed by mandatory sorts.** The `Π`, `Σ` and `ULift`
    casts computed with no check on their components' sorts, so the kernel accepted
    `λ e t. cast (Unit₁ → Type) (Unit₂ → Type) e t` and rejected its normal form ("cast
    between different universes"): subject reduction failed. The casts now compute only
    when the two domains (contents) are in one sort and the two codomains are, read off the
    sorts written in the terms: decided by the terms, and stable under level substitution
    (`≡` holds at every instance). Otherwise they are stuck (meta-review decision 1:
    stuck, as WizMeta's `Pi.cast`). The test "D2 (closed by mandatory sorts): …" checks
    the four probes in both kernels.
  * **Open gap 2: the elaborator.** It evaluates terms it has not marked yet, and it
    evaluates a suspended proof when it reads a value back into a term (the kernel must
    be able to check that term again). The read-back runs within a **step budget**
    (`--proof-steps N`, default 1 000 000 closure instantiations per proof; counted, not
    timed, so the same on every machine), and so do `#reduce`, hover and the
    elaborator's messages; a proof that runs out reads back as an error. The
    elaborator's direct evaluation of an unmarked proof has no bound: on a proof without
    a normal form, elaboration can still loop. Kernel error messages no longer evaluate
    proofs. None of this is on the path by which the kernel accepts a term.
* **What it costs (known failures).** Without regularity a cast at a **type variable**
  is stuck (TTobs behaviour): `cast e a = a` for `e : A = A`, "`J` computes on `refl`"
  at a variable family, and the definitional equations of functions defined by `match`
  on an *indexed* family whose result type is dependent and mentions a type variable:
  `Vec.map f (cons x xs)` is `cons (cast B B _ (f x)) (cast … (Vec.map f xs))`. So
  `Vec.map_map`, `Vec.get_set` and `Vec.get_map` can't be proved by computation.
  Decision (the user's): a propositional **`castRefl : cast A A e a = a`**, an axiom in
  the Prelude (CoreSpec §8.4a). It is consistent in the setoid model, doesn't compute,
  and is listed by `#print axioms`. With it the three theorems are back in `lib/Vec.wiz`
  (through `Vec.map_cons`, `get_cons_*` and `set_cons_*`), and so is `Lens.pair_putGet`
  in `lib/Optic.wiz`. Non-indexed types and constant
  motives are unaffected: recursors of non-indexed types have no cast, and indexed
  families get `T.recN`/`T.casesOnN` for motives independent of the scrutinee.

### K3. The size argument of `μ`/`ν` is never type-checked — **fixed** (`4605514`, both kernels)

The `mu`/`nu` rule ignores the size (`Check.lean:527`; `Kernel.wiz:1918, 1967, 2020`), so
a type `μ^s D i` with an ill-typed `s` is accepted. Sizes only matter to `sizeLe`, which
treats an unknown base as incomparable, so no exploit is known. The kernel should still
check `Γ⁰ ⊢ s ⇐ Size` (one line in each kernel).

**Fix**: both kernels now check `Γ⁰ ⊢ s ⇐ Size` in the `mu`/`nu` rule. Regression tests:
`MTm.sizeArgs` (`tt` and `Enum 2` as sizes are rejected) in the Lean verdicts and the
differential samples.

### Q1 / R1. Projections drop linear components — **fixed**: projections need an unrestricted pair (lin-proj; both kernels)

`p.2` on `p : (1 x : A) × B` uses `p` once and discards `x` (§7.1); `p.1` discards the
second component. In the `{0, 1, ω}` rig, `1` is documented as "exactly once"
(`Rig.lean:22`). Atkey's tensor has no projections. This cannot produce a proof of
`False` or break erasure (a dropped value is never needed), but it breaks the guarantee
that a linear resource is consumed. **Confirmed**: `def drop {A B : Type} (1 p : (1 x : A) × B) : B := p.2` is accepted,
while `def drop2 {A B : Type} (1 x : A) (y : B) : B := y` is rejected ("declared with
quantity 1 but used 0"). Fix:
allow `.2` only when the first field's quantity allows zero uses (`0 ≤ q`), and `.1`
only when the pair's second part is not linear; or reserve projections for pairs whose
quantities admit weakening.

**History.** `212aebf` made `p.2` count `p` as used ω times when the first field's
quantity doesn't allow zero uses. lin-fixes (PR #50, `mustUse`) did the same for `p.1`
when the second part *holds a field declared* with such a quantity, and hdl-fix (PR #58,
`mustUseType?`) decided that from the type, because evaluating the pair overflowed the
stack. Both rules asked the dropped part's declared quantities. The second component of a
Σ has none, so **R1** (the soundness audit) remained: `p.1` on `(1 p : A × Tok)` dropped
the bare `Tok`, and a projection of an *expression* was never tracked at all, so
`(act w).1` for `act : IO A` used `w` once and dropped the world `act` returns. Not a
duplication (no use after free), but "must be consumed" did not hold: a session endpoint
abandoned mid-protocol, a lock guard never released, a region never closed.

**Fix** (rule (b) of the audit; CoreSpec §7.1): **projections are available only on
unrestricted pairs.** Outside erased positions `t.1` and `t.2` use `t` ω times, whatever
the component types and whether `t` is a variable or an expression. A pair held at any
other quantity is taken apart with the split form, `let 1 (x, y) := p; …`, which accounts
for both components. This subsumes the two earlier rules: `mustUse`, `mustUseType?` and
the `.2` special case are removed from both kernels (and with them the last place where
the checker evaluated a pair to decide a usage). In erased positions (types, proofs,
arguments to 0 binders, and now also the other positions scaled by a constant 0: the
value of a `let` at 0, the first part of a pair at a 0 field, the scrutinee of a split at
0) projections stay free.

What it costs:

* `let (x, y) := p` without a quantity splits at ω; a linear pair needs `let 1 (x, y)`.
  The error at a rejected projection says which form to write.
* A pair at a quantity *variable* can't be projected (`ω ≤ q` fails for `q = 1`); it can
  be split at `q`.
* **A structure held at a quantity other than ω can't be consumed.** `s.field` is a chain
  of projections; `match` doesn't take a structure (or a tuple) apart linearly; and a
  nested `let 1 (x, y)` over the structure's Σ leaves its marker tail as a linear
  variable that nothing consumes. Before the fix the only thing that worked was reading
  exactly one field, which silently dropped the others: nothing sound is lost. Linear
  data is a tuple for now; linear matching is wishful
  (`/workspace/wiz-notes/wishful/linear-case.md`).
* Kernel.wiz has no split form, so its fragment can't consume a linear pair at all
  (CoreSpec §15); both kernels reject the same terms.
* Nothing in `lib/`, `examples/` or `selfhost/` needed a change: `lib/IO.wiz` already
  split the result of an action with `let 1 (a, w') := x w`.

**The same hole in the eliminators** (found by the linear-case design, probe `p05`):
`ind` charged its scrutinee once but binds the payload at ω, so raw `ind` on a scrutinee
held at 1 could duplicate or drop a linear token (`(1 t : Tok) → Tok × Tok` was
accepted); `sfix`, `scase`, `Desc.elim` and the seeds of `coit`/`scofix` had the same
shape. **Fixed** with the same rule: these eliminators use their scrutinee (seed) ω times
(CoreSpec §7.1, §9, §10; both kernels). `match` was not affected. Nothing in `lib/`,
`examples/` or `selfhost/` eliminated a linear scrutinee.

**Positions at 0** are checked erased and never evaluated; erasure used to evaluate the
scrutinee of a split at 0 (fixed), and the kernel and erasure now share the test for
"constant 0" (`QPoly.isErased`). `selfhost/Backend.wiz` erases the value of a `let` at 0.

**Usability regression, and what follows.** A one-field structure held at 1 could be read
soundly before (`structure Coin where value : Nat`; `c.value` dropped only the marker
tail); it can't now. Write such a wrapper as a definition (`def Coin : Type := Nat`) or a
tuple. The follow-up is a destructuring `let 1 (.mk a b) := s` compiled to nested splits
(`/workspace/wiz-notes/linear-case-design.md`). The accepted follow-up is the linear-case plan (`/workspace/wiz-notes/linear-case-design.md`): K2a (an unused variable may leave its binder when its type is `Unit`, so a linear `Unit` needs no consumer), re-encoding B of structures (the marker in a 0-quantity first component, so a nested `let 1` leaves no marker tail to consume), and a quantity on `scase` (`scase_π`: the scrutinee is used π times and its fields are bound at π·q), which gives structures a destructuring form and linear inductive values an eliminator.

Tests: "check: structural types" (kernel rules), "language" and "ffi" (surface programs,
the three audit probes, structures, erased positions and their erasure), and the
differential samples.

### Q2. Methods are scaled by the rig's default, not by ω — **fixed** (`a986c02`, Lean kernel)

`ind`, `Desc.elim`, `sfix`, `scofix`, `coit` scale their methods' usage by
`explicitDefault` (§9, §10). That is ω for `{0, 1, ω}`, so the `wiz` tool is fine. For the
`Nat` rig (exact counting) it is `1`, which under-counts a method that runs once per node.
The kernel is advertised as parametric in the rig, so this is a gap for those instances.

**Fix**: `QRig` has `many? : Option R`, the unrestricted quantity (ω for `{0, 1, ω}`,
`()` for the trivial rig, none for `Nat`). Methods are scaled by it; in a rig without one
a method may use local variables only in erased positions (`methodUsage`,
`Check.lean`). The self-hosted kernel has the fixed `{0, 1, ω}` rig, whose default is ω,
so it needed no change. Tests: "check: quantities" (a `coit` in the `Nat` rig whose step
captures an erased variable is accepted, a linear one rejected).

### Q3. Regularity by quotation assumes fewer than 100 000 variables — **fixed** (`b7e1736`, both kernels)

`sameVal` compares `quote 100000 A` and `quote 100000 B` (`Eval.lean`, `Kernel.wiz`); since
D1 it decides regularity at inert types and whether two `μ` types are of one family. With more than 100 000 variables in scope, `100000 - x - 1` truncates
to 0 for several variables, and two different types could quote equal. Unreachable in
practice; easy to fix (quote at the actual context size, which `vCast` doesn't have, or
compare with `conv`).

**Fix**: `sameVal` (both kernels) quotes at `max (lvlBound A) (lvlBound B)`, one above
the largest variable level `quote` can reach in either value (`Val.lvlBound` in
`Eval.lean`, `lvlBound` in `Kernel.wiz`; a closure counts only the environment entries
its body mentions). The bound can be too large, never too small. Cost: one extra walk of
the two values per `sameVal` (a perf measurement of the self-check is wanted).

### Q4. Description fields in smaller universes: subject reduction failed — **fixed** (see F5)

Decision (a), a kernel `ULift` former with the elaborator lifting small fields, is
implemented in both kernels: see **F5** in "Fixed issues" for the rules, the tests and the
costs that remain. The options that were weighed: (a) `ULift`, chosen; (b) cumulativity,
large and cross-cutting; (d) `marg` quantifying over the field's level, which needs a Π over
levels (`Setω`) that Wiz's core has no place for (levels are prenex parameters of globals).

---

### E1. Equality of descriptions (4g): `μ` injective in its description — **conjecture** (model obligation)

**What.** `vEqDesc` compares two description codes by their constructors, and `μ I D i ≡
μ I' D' i'` computes to `(I, D, i) = (I', D', i')` at the type of codes for every
pair of families (CoreSpec §8.4b), with `cast` between them computing constructor by
constructor. This makes `μ` injective in `D : Desc_l I : Type (l+1)`, with `μ D i : Type l`:
the shape of Hur's paradox (`xtt-cubical-attacks.md` D4).

**Argument (not a proof).** The setoid model of [PT22]/[PT23] with `Type l` as an
inductive-recursive universe of codes `U_l`, extended with a *nested* inductive
`Desc(U_l, I)` of description codes (fields are codes of `U_l`, `E : El S → Desc`) and a
code `μ (I : U_l) (D : Desc(U_l, I)) (i : El I)`. Code equality is the structural
relation the kernel computes; different constructors are unrelated; cast is by recursion
on the element. `Desc(U_l, I)` mentions only codes of `U_l` and never families over `U_l`
(field types are exactly in `Sort (l+1)`, F5/Q4), as for Π-codes, whose injectivity TTobs
already has. At `l = 0`, `Prop : Sort 1` is a valid field type, which gives an injection
`(Prop → Prop) ↪ Type`; that is the shape of CCobs's Π-injectivity over a `Prop` domain
(model: [PT23]; classically `Prop ≅ 2`), not Hur's `(Type → Type) ↪ Type`. Proof fields
are lifted propositions compared by equivalence, so the A0 issue doesn't return.

**Obligations.** (1) The definition of `U_l` with `Desc(U_l, -)` and the structural
relation: not plain IR, since `El (μ I D i)` is an inductive family (the initial algebra
of `⟦D⟧`) defined inside the recursive definition of `El` (as in generic-universe
constructions, Gratzer 2022, which Pujet's CIC^obs model uses), with impredicative `Prop`
(as in [PT23]); (2) that
equality of `μ` codes is equality of `(I, D, i)` at `(J : Sort (l+1)) × Desc J × J`, so
the cast's payload equation is one `transp` (well typed); (3) quantities as part of
codes (as for Π).

**Stability.** The rules decide the shape of the result by the heads of the two codes
only: no syntactic equality, and no simplification of `True` components (a theory review
on 2026-11-10 showed both are unstable under substitution). The cost is that `μ D i ≡ μ D
i'` is no longer `i = i'` (README 4g).

**Tests.** `Tests/Elab.lean`, group `desceq` (both kernels where the self-hosted kernel
is reachable): `List Nat ≡ List Bool` refuted through `Nat ≡ Bool`; `UIntN 8 ≡ UIntN 16`
refuted; casts between `List A` and `List B` compute elementwise; the Abel–Coquand box
with two different but equal descriptions checks; the Hur-style encoding over `Type` at
`l = 0` is rejected by the field-level rule.

### R3. A representation chosen by what conversion ignores — **partly fixed; two parts open**

* **What.** Erasure chose representations by a binder name (`phantom✝`: erased), an
  `Enum` label (`fields✝`: the Σ before it unboxed) and the display name on a `μ` (`Nat`:
  a number; a type with `implemented_by` on its constructor: a native value). Conversion
  ignores all three, so the kernel accepted conversions between types with different
  representations and `#eval` and compiled code gave wrong values (soundness audit, R3;
  not a proof of `False`: the kernel is not involved).
* **Fixed, in erasure only** (`Compiler/Erase.lean`, `Run.lean`'s readback, `◾` applied
  is `◾` in `runtime/wiz.c` and the IR interpreter): erased functions into `Unit` by
  quantities (`erasedFunTy`), `Nat` by the description's shape (`natShaped`), one function
  deciding unboxing at every site. Group `repr`.
* **Refused instead of miscompiled:** a description whose first field has an abstract type
  (`def mkD (S : Type) F := Desc.arg 1 S F`, later used at `S := Enum …`). Whether a
  value's object carries the constructor tag is decided from the type at a known type and
  from a mark in the run-time description in generic code, and the two disagreed
  (a wrong value in `#eval`, a crash compiled). Erasure now reports an error.
* **Open 1: Σ unboxing is not stable under substitution**, with the marker or by shape:
  generic code over `A × B` meets a structure's bare field. It is off by default
  (`--unbox-structs`, 22i); the layout needs a new structure encoding to come back.
* **Open 2: native representations** (`attribute [implemented_by mk get] T.mk`, 22d) are
  still found by the `μ`'s display name: a copy of `UIntN`'s declaration is convertible to
  it and has the model's object, and compiled code then computes wrong values. Shape
  cannot decide this one (it needs the registration attached to something conversion
  compares). `/workspace/wiz-notes/repr-shape.md`, §4.

## 5. Stuck but sound

These are places where the kernel deliberately does **not** compute, so some true
equations are not provable by computation. They are incompleteness, not unsoundness.

* **A Π/Σ whose component sort depends on a level parameter** that may be `0`: type
  equality and `cast` need to know whether a type is a proposition (§8.3), and stay stuck.
  (A Π/Σ without a sort annotation, which used to be stuck too, no longer exists:
  mandatory sorts.)
* **Neutral types**: `a =_X b` and `cast X Y e t` for a variable `X` are stuck.
* **`μ ≡ μ`, `ν ≡ ν`** are stuck when the levels are not known equivalent or the sizes
  are not equal as conversion sees them (`∞` against `↑s`, two different size variables). Since 4g
  they compute otherwise (E1).
* **Equality at `ν`** is stuck (no bisimulation).
* **`Size ≡ Size`, `Qty ≡ Qty`** are stuck in the Lean kernel (in `Kernel.wiz`, `Size`
  is wrongly `False`: O1).
* **Π/Σ types whose quantities are not literals** (quantity variables that can't be
  compared): type equality is stuck.
* **Casts at a level `u` that might be 0**, `Sort u ≡ Sort v` for different parameters.
* **Regularity at an inert type with an open index** (P1): `cast (Fin n) (Fin n) e k` for
  variables `n`, `k` is stuck as a *value* (the evaluator's rule fires only at ground
  types, so that its firing is stable under substitution), and equal to `k` in
  *conversion* (InReg_conv, D1). A cast at a type that is not inert (a type variable, a
  type with a `Prop` field or a function) stays; `castRefl` proves that equation
  propositionally.
* **The sorts decide between rules** (P1 inventory, U5). `propSort?` reads a Π/Σ's
  component sorts. They are mandatory and conversion compares them, so convertible types
  are treated alike (before, an unannotated type and a convertible annotated one were
  treated differently; `/workspace/wiz-notes/p1-stable.md`).
* **Conversion is incomplete** where proof irrelevance meets computation (e.g. a `split`
  stuck on one proof and computing on another). Incompleteness only.

---

## 6. Planned tiers (cubical, XTT, STC)

None of these is implemented. Their status is **design and conjecture**:

* **XTT and univalent cubical type theory as tiers** (`Pre ⊇ K ⊇ Set`):
  `/workspace/wiz-notes/xtt-cubical-fragments.md`. XTT has a **canonicity** proof only
  (Sterling, Angiuli, Gratzer, FSCD 2019 and *A Cubical Language for Bishop Sets*, LMCS
  18(1), 2022; venue checked); no
  normalisation or decidability proof exists for XTT. The combined three-tier model is a
  **conjecture**.
* **Adversarial review** of that design: `/workspace/wiz-notes/xtt-cubical-attacks.md`.
  It found the live `False` that became F1 (A0), and several design-level
  counterexamples (A1, A2, B1–B8) that the plan must fix before it is implemented. Its
  D-items (D1–D5) are metatheoretic gaps with no counterexample and no proof.
* **The expert question** about the three-tier model:
  `/workspace/wiz-notes/xd7-review-brief.md` (decision XD7). Its §1.9 "discrete sets"
  candidate model is new and **unreviewed**.
* **STC / normalisation plan**: `/workspace/wiz-notes/stc-plan.md` (M0–M5): a
  specification of a fragment F0 in Lean, then normalisation by logical relations and an
  extracted checker. It targets modules with regularity off or a predicative `Prop`.
  Nothing of it exists yet.

---

## 7. Kernel trust

The **de Bruijn criterion** asks that a proof checker have a small, independent kernel
that checks everything. Wiz's situation:

* **Size.** The Lean kernel is `Wiz/Core/{Term,Value,Level,QPoly,Usage,Eval,Conv,Check,
  Templates}.lean` plus `Wiz/Rig.lean` and `Wiz/Rig/Instances.lean`: about **3 200
  lines**, about 2 500 without blank lines and line comments. (`Pretty.lean` and
  `Raw.lean` are not trusted. `Term.hasVar`, which `Ctx.instArg` relies on, and the
  traversal `Term.mapChildrenM`/`forChildren`, which `hasVar` and `Val.lvlBound` rely on,
  are in `Term.lean`: `hasVar` was moved there from `Pretty.lean` when the kernel started
  to depend on it. A constructor missing from `mapChildrenM` is a kernel bug: see F7.) This includes the computation rules of OTT, descriptions
  and sizes, so it is larger than a Lean-4-style kernel per feature.
* **Two kernels.** `selfhost/Kernel.wiz` (about 2 200 lines) is an independent
  reimplementation in Wiz of a fragment (CoreSpec §15). It was written from the Lean
  kernel, so it can share design mistakes (it shared both F1 and F2), but not
  implementation slips, and it has one of its own (O1).
* **Differential test** (group *selfhost*, "the Wiz kernel agrees with the Lean kernel (400
  random terms)", and "… declarations at symbolic levels like the Lean kernel"): the
  hand-picked `MTm.samples` (including the F1 and F2 attacks) and 400 random terms,
  checked by both kernels, must get the same verdict (the printed type or `error`).
  It compares *verdicts*; it cannot find a bug both kernels share, and its generator does
  not reach every former (it missed O1).
* **What the kernel does not check** (CoreSpec §16): axioms (including C imports;
  `#print axioms d` lists those `d` depends on), the `builtin` registrations of the
  toolchain's library (below; a registration anywhere else is an axiom, reported by
  `#print axioms`), the templates and the kernel's own generated types, and everything
  after type checking (erasure, the backends). Partial definitions are no longer
  trusted: each comes with a witness the kernel checks.
* **Trusted registrations** (`lib/Prelude.wiz`, reviewed once against the native
  operations `natNative?` in `Eval.lean`, which follow Lean's `Nat`): `nat := Nat`,
  `nat.zero := Nat.zero`, `nat.succ := Nat.succ` (numerals); `nat.pred := Nat.pred`
  (`0 ↦ 0`), `nat.add := Nat.add`, `nat.sub := Nat.sub` (truncated: `subFrom m n` is
  `pred` applied `m` times), `nat.mul := Nat.mul`, `nat.div := Nat.div` (`divGo` with
  fuel `n`, enough since `n / m ≤ n`; `n / 0 = 0`), `nat.mod := Nat.mod`
  (`n - m * (n / m)`, so `n % 0 = n`), `nat.pow := Nat.pow`, `nat.land`, `nat.lor`,
  `nat.xor` (`Nat.bitwise` with fuel `a + b`, at least the number of bits),
  `nat.shiftLeft` (`a * 2^n`), `nat.shiftRight` (`a / 2^n`), `nat.log2` (`log2Go` with
  fuel `n`; `log2 0 = 0`); `nat.beq := Nat.beq` and `nat.blt := Nat.lt` (the kernel
  decides `a == b` or `a < b` natively, then evaluates the definition at `0` and `0` or
  `1`, so the result is the definition's own `Bool`: correct exactly when the definition
  is equality, resp. `<`, which `Nat.beq` and `Nat.lt` are, by their equations). The
  kernel computes only these natively; `memo := memo` (`memo f = f` to the kernel) and
  `string := String` affect only the runtime representation and literals.
* **Compiled equations of recursive definitions** (`Decl.impl`, T1): no longer trusted:
  the kernel checks their type and that they compute what the definition computes
  (`checkImplAgrees`). What erasure does to them afterwards (`Compiler/Push.lean`, checked
  again by the kernel for typing) belongs to the compiler, like the rest of erasure.
* **Implementations for compiled code** are outside the kernel: `attribute
  [implemented_by g] f` (stage 22b), including the native representations it registers
  for a type (`attribute [implemented_by mk get] T.mk`, builtin keys `repr:T:…`, used by
  `UIntN`/`IntN` in `lib/Word.wiz`) and the word natives (`UIntN.addNative` …,
  `runtime/wiz.c`). The kernel never sees them (`vBuiltin?` acts only on `nat.*` keys),
  so they can't prove anything; they are trusted to agree with the definitions, as in
  Lean, and the tests compare the two (`#eval` runs the definitions, compiled code the
  natives). They are not `builtin` commands, so the registration checks don't apply.
  `#print axioms d` lists the ones `d` depends on, the library's too, marked `native`
  (`native f := g`, `native T := mk/get`).
* **Termination** of the kernel is not proved; all evaluation functions are `partial` in
  Lean.
* **The kernel does not evaluate proofs (P2).** `eval` suspends the equation of a `cast`,
  the proofs of a `transp` and every marked proof, and the kernel requires the marker
  wherever a proof would otherwise be evaluated (CoreSpec §8.6a). Pujet–Tabareau's
  decidability result for impredicative OTT (CCobs, [PT23]) and Pujet–Leray–Tabareau's
  with regularity ([PLT25], Theorem 5.6, for Π, ℕ, ⊥, `Ω`, ∃) are proved for algorithms
  that never normalise proofs, so a Wiz version of those theorems could be about this
  kernel. What stands between: Wiz's data types are not in the fragment those theorems
  cover (D1, P2). (Sorts are mandatory since the mandatory-sorts change, closing U5.) In [PT23]'s words (§6.1): "we never
  perform reduction in the proof-irrelevant layer".
  (`/workspace/wiz-notes/p2-proofs.md`, `prf-marker.md`, `plt-vs-inert.md` §6.)

## 8. Testing evidence

* **Negative tests**: the test suite has about 55 cases in `Tests/Elab.lean` that must be
  *rejected* (`fails …`), plus the quantity and structural cases in `Tests/Check.lean`
  (e.g. "linear variable used twice is rejected", "linear pair projected twice is
  rejected", "Type : Type is rejected").
* **Attacks that are regression tests**: F1 and F2 above (both kernels).
* **Adversarial review**: `xtt-cubical-attacks.md` (it found F1). Its "negative tests to
  add" list concerns the planned tiers.
* **D1**: the Abel–Coquand programs (direct and nested box) are regression tests in both
  kernels: they check without regularity and loop with it.
* **Self-check**: the self-hosted frontend checks its own source (group *selfhost*). This
  shows the kernels accept a large realistic program; it is not evidence against
  unsoundness.
* **Not done**: fuzzing for proofs of `False` (random well-typed terms of type `False`),
  property tests of the computation rules (e.g. that `vEq`/`vCast` results are well
  typed), or a mechanised model.

## Probes

Small files run with `wiz check` (via `heavy`) while writing this page, in
`/tmp/core-spec-probes/` (copied into the report, not committed):

Small files checked with `wiz check` (through `heavy`, `--no-cache`, built from
`9717950`) while writing this page. They are reproduced inline above; none is committed
as a test yet (each should become one when its issue is fixed).

| probe | result |
|---|---|
| `reflTy Size`, `absurd Empty (reflTy Size)` in `Kernel.wiz` (O1) | accepted: `False`, `Empty0` |
| `#reduce Size = Size` in the Lean kernel | stuck: `Size = Size` |
| `partial def bad : T .f` + `boom : False` (O2) | accepted: `boom : False` (now rejected: no witness, F3) |
| `partial def bad2 : False := bad2` (control) | rejected |
| `partial def bad : T .t → T .f` (O2) | accepted (now rejected, F3) |
| wrong `builtin nat.add` (O3) | accepted: `bad : False` (now an axiom: warned, listed by `#print axioms`, F4) |
| `builtin nat := E` (empty) + `(0 : E)` (O3) | `wiz check` crashes (stack overflow) (now an error, F4) |
| `p.2` on a linear pair (Q1) | rejected since `212aebf` (was accepted) |
| `p.1` on a linear pair whose second part holds a linear field (Q1) | rejected (lin-fixes; was accepted) |
| `p.1` on `(1 p : A × Tok)`, on `(1 p : (1 a : A) × Tok)`, and `(act w).1` (R1; `soundness-probes/r1-linear-fst.wiz`) | rejected (lin-proj: projections need an unrestricted pair; were accepted) |
| `Desc.arg 1 True …` (Q4, fixed: F5) | rejected by the elaborator (field must be in `Type ?u`) and now by both kernels (`MTm.smallField`: `D` and `getS D` rejected; the lifted `D'` accepted, `getS D'` is `ULift True : Type`) |

## How to report a soundness bug

1. **What counts.** A closed term the kernel accepts at type `False` (or `Empty`, or
   `(A : Type) → A`) without axioms, `partial`, or `builtin` beyond the Prelude's; a
   well-typed term on which the kernel loops or crashes; two kernels disagreeing; a
   quantity violation (a `0` variable used at run time, a linear one used twice).
2. **Make it small.** Remove declarations until it stops failing. Prefer core primitives
   to surface sugar, so it is clear whether the kernel or the elaborator is at fault.
3. **Check both kernels** if you can: the Lean kernel through `wiz check`, `Kernel.wiz`
   through an `MTm` term in the differential test (`Tests/Elab.lean`, `MTm.samples`).
4. **File it** as a note in `/workspace/wiz-notes/` (or tell the owner) with: the file,
   the command, the output, the commit, and which rule you think is wrong (cite
   CoreSpec.md's section).
5. **Fix it with a regression test** in both kernels: a `fails` case in the right group,
   and the term in `MTm.samples` so the differential test runs it. Then update this page:
   move the issue to "Fixed issues" with the commit and the test names.

## References

As in [CoreSpec.md §17](CoreSpec.md#17-references): [Atkey18], [AC20], [CDMM10], [AVW17],
[PT22], [PT23], [PLT25], Agda #3026 (checked); [ML84], [AMS07], Gilbert et al. (not
re-checked).
