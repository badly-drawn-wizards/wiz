# Soundness and metatheory status

This page says what is known about whether Wiz's core is **consistent** (no closed proof
of `False`), whether its type checking **terminates**, and whether its **quantities**
mean what they claim. It is meant to be honest first: if something is not proved, it says
so. The calculus itself is specified in [CoreSpec.md](CoreSpec.md); section numbers
written "§n" refer to it.

The state described here is the `solutions` branch at commit `9717950` (2026-11-09), plus
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
* **Type checking can fail to terminate.** Definitional regularity together with an
  impredicative `Prop` and proof-irrelevant equality is the Abel–Coquand setting [AC20],
  and the D1 experiment produced a closed program on which both kernels loop. This is an
  open issue (decision D1).
* **Two proofs of `False` in the kernel have been found and fixed** (propositions
  compared by shape; `∞ < ∞`), each with regression tests in both kernels.
* **Three proofs of `False` were found while writing this page, and confirmed by
  running them** (see "Open issues" and "Probes"):
  * **O1** (fixed in `c079d1b`): the self-hosted kernel reduced `Size ≡ Size` to
    `False`, so `reflTy Size : False` there (the Lean kernel was not affected);
  * **O2**: a `partial def` at an empty instance of an indexed family passes the
    elaborator's inhabitedness check, and the kernel takes it as an axiom
    (`boom : False`, no axioms written);
  * **O3**: a user's `builtin nat.add := K` with a definition that disagrees with native
    addition proves `False`.

  O2 and O3 are not bugs in the kernel's rules: in both, the kernel accepts a declaration
  on trust (an axiom the elaborator vouched for; an unchecked registration). They are
  still closed proofs of `False` in the language. Several smaller gaps are listed too.

---

## 1. Ingredients

| ingredient | status | source and notes |
|---|---|---|
| Π, λ, application, `let`, Σ with η, `Unit` with η | **published** | Martin-Löf type theory [ML84]; η for Σ and Unit with type-directed conversion is standard (unverified which paper first). |
| Universes `Sort l`, `imax`, impredicative `Prop`, non-cumulative, universe-polymorphic declarations | **published** for CIC-like systems; **folklore** for Wiz's exact algorithm | Lean 4's universe design; Wiz's level normaliser (§4) is sound by construction (it case-splits) and incomplete for `imax`, as in Lean (unverified against Lean's source). |
| Definitional proof irrelevance for `Prop` | **published** | [PT22], [PT23] (TTobs, CCobs); Gilbert et al. POPL 2019 (unverified). Wiz has no inductive propositions, so the Lean 4 `Acc` problem does not arise. |
| Observational equality: `eq` computing by type, `cast`, `transp`, funext, propext | **published** | [PT22] (predicative TTobs), [PT23] (impredicative CCobs: decidability of conversion). Earlier: [AMS07]. |
| Propositions compared by equivalence inside type equality (§8.3) | **conjecture** | This is how TTobs treats `Prop` (per the review `xtt-cubical-attacks.md` A0; not re-checked in [PT22]). Wiz's version depends on **sort annotations** that the kernel checks; that mechanism is Wiz's own. |
| Quantities in type equality (`(1 x : A) → B ≢ (ω x : A) → B`) | **conjecture** | Not in any OTT paper we know. It is consistent with a model where quantities are part of a type's code. |
| Regularity `cast A A e t ≡ t` (evaluation, by syntactic equality; conversion, `unCast`) | **open issue** for normalisation; **folklore** for consistency | [AC20]: with impredicative `Prop` and irrelevant equality, normalisation fails. Our notes say TTobs/CCobs do **not** have definitional regularity (unverified against the papers). See D1. |
| Enumerations, `ecase`, equality of tags | **folklore** | Standard finite types. Labels are ignored (`Enum [a,b] ≡ Enum [c,d]`), which is harmless: a model can interpret `Enum` by its size. |
| Descriptions (`ret`, `arg`, `rec`, `hrec`), `Desc.elim`, `μ`, `ind` | **published** for levitated descriptions without quantities [CDMM10]; **conjecture** with quantities and with `Desc` as a primitive | The eliminator `Desc.elim` is large (into any `Sort v`). Field quantities and the quantity-polymorphic `marg` are Wiz's own. See also Q4 (subject reduction). |
| Observational equality at `μ` (`con x = con y ↦ x = y`) | **conjecture** | Natural, follows the TTobs pattern for inductive types; [PT22] treats ℕ and (unverified) general inductives differently. `μ ≡ μ` as types is deliberately stuck. |
| Sized types: `Size`, `∞`, `↑`, `Size<`, subtyping, `sfix`, `scase` | **published** in outline [AVW17]; **conjecture** for Wiz's rules | Wiz's order and the D2 rule are its own (§10.1). Unfolding only on constructors follows Abel's MiniAgda (unverified). |
| Coinduction: `ν`, `out`, `cocon`, `coit`, `scofix` | **folklore** | Sized coinduction is Abel's; Wiz's exact rules have no paper. Equality at `ν` is stuck. |
| QTT usage accounting (the rig, scaling, subusaging) | **published** for Atkey's system [Atkey18] | Wiz differs: quantities are terms with polymorphism (§5.2), branches are joined (§5.3), eliminators scale methods by the default quantity, projections on pairs (§7.1), "σ = 1 everywhere, then discard" (§5.4). The differences are **conjecture**, and one is an open issue (Q1). |
| Quantity polymorphism (`Qty`, polynomial usages, `≤` by trying every assignment) | **conjecture** | Sound for finite rigs if each assignment is a valid instance (it checks them all). No paper. |
| Numerals and native arithmetic | **folklore**, conditional on correct `builtin` registrations | See K2: the registrations are trusted. |
| Glued (lazy) unfolding, `lazyInd` | **folklore** | An implementation technique; it must give the same answers as eager unfolding. Not proved. |

## 2. Interactions

| interaction | status | notes |
|---|---|---|
| QTT + dependent types | **published** [Atkey18] | Wiz's simplified σ-handling: conjecture (§5.4). |
| QTT + observational equality | **conjecture** | No published system combines them. Proofs and types are erased (usage 0), `cast` passes its argument's usage through. Erasure soundness (a 0-quantity value is never needed at run time) is what QTT should give; it is not proved for Wiz. |
| QTT + descriptions | **conjecture** | Fields carry quantities; the payload Σ uses them; methods are scaled. No paper. |
| QTT + sized types + coinduction | **conjecture** | Sizes are erased (always quantity 0). No paper. |
| Observational equality + impredicative `Prop` + regularity | **open issue** (normalisation) | D1, below. Consistency is not known to fail. |
| Observational equality + descriptions (`eq` at `μ`, `cast` between `μ` types by regularity only) | **conjecture** | `μ ≡ μ` stuck; `cast` between μ types computes only by regularity. The D1 loop uses exactly this. |
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
  non-proposition (§8.3, §8.4). Commit **`1b6dc00`** on `solutions` ("Fix a proof of
  False: type equality compares propositions by equivalence"; `cfac255` on `master`).
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
  `↑ᵏ x` for a variable `x : Size< u`. Commit **`fb9074d`** on `solutions` ("Decision D2:
  ∞ is not below itself (both kernels)"; `d521cfa` on `master`).
* **Regression tests.**
  * group *sized types*: "∞ is not a size below ∞";
  * group *selfhost*: "∞ is not below itself (and both kernels agree on it below)"
    (`MTm.sizeInf`: 5 rejected, 5 accepted), and `MTm.sizeInf` is in the differential
    samples.
* **Status of sizes otherwise:** conjecture. The atlas still lists `sized-types`,
  `sized-recursion`, `sized-corecursion`, `sh-kernel-sizes` and `sh-kernel-coinduction` as
  "known-issue" for `∞ < ∞`; that is out of date.

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

### O2. Partial definitions trust an elaborator check that can be fooled — **open issue (proof of `False`, confirmed)**

`partial def f : T := …` adds `f : T` as a kernel **axiom** (§13). Only the elaborator's
`inhabitedTy` (`Elab/Command.lean:576`) stands between that and `partial def bad : False
:= bad`. It decides inhabitation by the *head* of a type: a type headed by a name `T`
counts as inhabited if *some* constant's type ends in `T …` (`byConstant`), whatever the
indices, and inside a Π any type headed by the same name as a domain counts as inhabited.
So for an indexed family with an empty instance:

```
inductive B where | t | f
inductive T : B → Type where | mk : T .t
partial def bad : T .f := bad          -- T.mk : T .t makes "T …" look inhabited
```

`T .f` is empty, and an inhabitant of it gives `False` by `match`:

```
def boom : False := match bad with
  | .mk => absurd ()
#check boom                            -- boom : False   (CONFIRMED, `wiz check`)
```

The control `partial def bad2 : False := bad2` is rejected ("its type must be visibly
inhabited"), and `def ok (x : T .f) : False := match x with | .mk => absurd ()` is
accepted (it is correct: `T .f` is empty). So the hole is in `inhabitedTy`. The same check
also accepts `partial def bad : T .t → T .f := bad` (the domain's head `T` is assumed
inhabited in the codomain). Fix: make the kernel check partial definitions' types against a
witness the elaborator supplies, or make `inhabitedTy` compare the indices (use
`conv`), and add the file above as a negative test.

### O3. `builtin` registrations are trusted — **open issue (proof of `False` from a user registration, confirmed)**

`builtin nat := N` makes numerals have type `N`; `builtin nat.add := f` makes
`f 2 3` compute natively. Nothing checks `N` or `f` (`Elab/Command.lean:937–944`;
`vBuiltin?`, `vNatOp`, `Eval.lean:76, 386`). A wrong registration proves `False`, for
example by registering an empty type as `nat` (numerals inhabit it) or an `add` whose
definition disagrees with native addition (a lemma proved by unfolding the definition is
refuted by native computation at literals). **Confirmed**:

```
inductive N where
  | zero
  | succ (n : N)
def K (a b : N) : N := a
builtin nat := N
builtin nat.zero := N.zero
builtin nat.succ := N.succ
builtin nat.add := K
def h (n : N) : K n 3 = n := refl n     -- by K's definition
def bad : False := absurd (h 2)         -- K 2 3 computes natively to 5, so h 2 : 5 = 2 ↦ False
#check bad                              -- bad : False
```

(`#reduce K 2 3` prints `5`.) Registering an empty type as `nat` and writing a numeral at
it (`def E : Type := Empty; builtin nat := E; def bad : False := absurd (0 : E)`) crashed
`wiz check` with a stack overflow instead (where, not investigated). Registrations should be treated like axioms: listed,
restricted to the Prelude, or checked (the native operations can be checked against the
definitions on the registration's own terms only by proof, so restricting them is
simpler).

### D1. Regularity + impredicative `Prop` + irrelevant equality: type checking loops — **open issue (normalisation)**

* **Question.** Abel and Coquand [AC20] show that an impredicative `Prop`, a
  proof-irrelevant equality and a cast that reduces whenever the two types are
  definitionally equal (regularity) break normalisation. Wiz has all three.
* **Result** (`agent/d1-regularity`, notes in `/workspace/wiz-notes/d1-experiment.md`,
  not merged at `9717950`): their literal term does **not** loop in Wiz (a cast between
  two visible propositions applies the equivalence instead of using regularity), but
  wrapping the proposition in a one-field `μ` type does: regularity then fires at a type,
  and **both kernels loop while type checking a closed, axiom-free program**. The tests on
  that branch are "D1 (Abel–Coquand): checking a closed program does not terminate" and
  "D1 (Abel–Coquand): the Wiz kernel does not terminate on the program either (and checks
  it without regularity)" (group *observational equality* / *selfhost*).
* **What this means.** Non-termination of the checker, not a known proof of `False`.
  Consistency is not known to fail, but the usual route to consistency (normalisation)
  is unavailable while regularity is on.
* **Options under evaluation** (prototype flags on that branch, off by default):
  R1 regularity only at non-propositions (no effect: already so); **R2** regularity only
  along visible reflexivity proofs (blocks the loop); **off** (TTobs; blocks the loop);
  R3 predicative `Prop` (only a measurement; whether it restores normalisation is
  Abel–Coquand's open question). Fallout on examples, `lib` and selfhost was 0 errors for
  R1, R2 and off. The decision is the owner's (D1).

### K3. The size argument of `μ`/`ν` is never type-checked — **open issue (de Bruijn criterion)**

The `mu`/`nu` rule ignores the size (`Check.lean:527`; `Kernel.wiz:1918, 1967, 2020`), so
a type `μ^s D i` with an ill-typed `s` is accepted. Sizes only matter to `sizeLe`, which
treats an unknown base as incomparable, so no exploit is known. The kernel should still
check `Γ⁰ ⊢ s ⇐ Size` (one line in each kernel).

### Q1. Projections drop linear components — **open issue (linearity, not consistency)**

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

### Q2. Methods are scaled by the rig's default, not by ω — **open issue (non-default rigs only)**

`ind`, `Desc.elim`, `sfix`, `scofix`, `coit` scale their methods' usage by
`explicitDefault` (§9, §10). That is ω for `{0, 1, ω}`, so the `wiz` tool is fine. For the
`Nat` rig (exact counting) it is `1`, which under-counts a method that runs once per node.
The kernel is advertised as parametric in the rig, so this is a gap for those instances.

### Q3. Regularity by quotation assumes fewer than 100 000 variables — **open issue (theoretical)**

`vCast` compares `quote 100000 A` and `quote 100000 B` (`Eval.lean:635`;
`Kernel.wiz:996`). With more than 100 000 variables in scope, `100000 - x - 1` truncates
to 0 for several variables, and two different types could quote equal. Unreachable in
practice; easy to fix (quote at the actual context size, which `vCast` doesn't have, or
compare with `conv`).

### Q4. Description fields in smaller universes: subject reduction fails — **open issue (no exploit known)**

`arg q S D` accepts `S : Sort k` with `k ≤ l+1`, but `Desc.elim`'s `marg` expects
`S : Sort (l+1)`, and universes are not cumulative (§9.1). So `Desc.elim` on such a
description produces a term that is not well typed, e.g. a `getS : Desc Unit → Type` that
returns `True : Prop`. **Not reproduced**: the surface elaborator rejects
`Desc.arg 1 True …` (it expects the field in `Type ?u`), so building it needs a core term;
this finding is from reading the code only. No proof of `False` is known from it. A model with cumulativity would justify it; Wiz has none.
Options: require `k ≡ l+1` (lift small fields), or quantify `marg` over the field's level.

---

## 5. Stuck but sound

These are places where the kernel deliberately does **not** compute, so some true
equations are not provable by computation. They are incompleteness, not unsoundness.

* **Π/Σ without a sort annotation.** Type equality and `cast` need to know whether a type
  is a proposition (§8.3). Without an annotation the equation stays stuck. At `9717950`
  the elaborator leaves several internally built Π/Σ without one. The branch
  `agent/elab-sorts` (commit `31395a2`, not merged at `9717950`) annotates them using the
  kernel's `typeSort?`, except "a Π/Σ under a `fun` whose variable's type isn't written
  down, or one that still mentions a metavariable" (its README 4c text).
* **Neutral types**: `a =_X b` and `cast X Y e t` for a variable `X` are stuck.
* **`μ ≡ μ`, `ν ≡ ν`, `Desc ≡ Desc`** are always stuck (no structural comparison of
  descriptions; a design decision to avoid committing to injectivity of `μ`, see
  `xtt-cubical-attacks.md` D4).
* **Equality at `ν`** is stuck (no bisimulation).
* **`Size ≡ Size`, `Qty ≡ Qty`** are stuck in the Lean kernel (in `Kernel.wiz`, `Size`
  is wrongly `False`: O1).
* **Π/Σ types whose quantities are not literals** (quantity variables that can't be
  compared): type equality is stuck.
* **Casts at a level `u` that might be 0**, `Sort u ≡ Sort v` for different parameters.
* **Conversion is incomplete** where proof irrelevance meets computation (e.g. a `split`
  stuck on one proof and computing on another). Incompleteness only.

---

## 6. Planned tiers (cubical, XTT, STC)

None of these is implemented. Their status is **design and conjecture**:

* **XTT and univalent cubical type theory as tiers** (`Pre ⊇ K ⊇ Set`):
  `/workspace/wiz-notes/xtt-cubical-fragments.md`. XTT has a **canonicity** proof only
  (Sterling, Angiuli, Gratzer, FSCD 2019 and LMCS 2022, as reported in the note); no
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
  `Raw.lean` are not trusted.) This includes the computation rules of OTT, descriptions
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
* **What the kernel does not check** (CoreSpec §16): axioms (including C imports),
  partial definitions' inhabitedness (O2), `builtin` registrations (O3), the templates
  and the kernel's own generated types, the size of `μ`/`ν` (K3), and everything after
  type checking (erasure, the backends).
* **Termination** of the kernel is not proved and is known to fail (D1); all evaluation
  functions are `partial` in Lean.

## 8. Testing evidence

* **Negative tests**: the test suite has about 55 cases in `Tests/Elab.lean` that must be
  *rejected* (`fails …`), plus the quantity and structural cases in `Tests/Check.lean`
  (e.g. "linear variable used twice is rejected", "linear pair projected twice is
  rejected", "Type : Type is rejected").
* **Attacks that are regression tests**: F1 and F2 above (both kernels).
* **Adversarial review**: `xtt-cubical-attacks.md` (it found F1). Its "negative tests to
  add" list concerns the planned tiers.
* **D1 experiment**: the Abel–Coquand programs, on `agent/d1-regularity`.
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
| `partial def bad : T .f` + `boom : False` (O2) | accepted: `boom : False` |
| `partial def bad2 : False := bad2` (control) | rejected |
| `partial def bad : T .t → T .f` (O2) | accepted |
| wrong `builtin nat.add` (O3) | accepted: `bad : False` |
| `builtin nat := E` (empty) + `(0 : E)` (O3) | `wiz check` crashes (stack overflow) |
| `p.2` on a linear pair (Q1) | accepted; dropping a linear variable directly is rejected |
| `Desc.arg 1 True …` (Q4) | rejected by the elaborator (field must be in `Type ?u`); kernel path not probed |

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
[PT22], [PT23], Agda #3026 (checked); [ML84], [AMS07], Gilbert et al. (not re-checked).
