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
* **Regularity is off (D1).** Definitional regularity together with an impredicative
  `Prop` and proof-irrelevant equality is the Abel–Coquand setting [AC20], and the D1
  experiment produced a closed program on which both kernels looped. Decision D1 (a):
  regularity is off in both kernels, `cast` computes on data constructor by constructor,
  and the program now checks. One departure from the published "off" theory remains, a
  **conjecture**: regularity is kept at *inert* (first-order data) types (D1 below; now argued relative to the system without regularity, with one incompleteness found).
* **Three proofs of `False` in the kernel have been found and fixed** (propositions
  compared by shape; `∞ < ∞`; quantities that differ only by a variable, F6), each with
  regression tests. A failure of
  subject reduction for small description fields (Q4) is fixed too (F5, `ULift`).
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
| Regularity `cast A A e t ≡ t` | **off** by default (D1); kept at inert types: **conjecture** (argued relative to the regularity-off system; algorithmically incomplete, D1); propositionally, the axiom `castRefl`: **folklore** (setoid model) | [AC20]: with impredicative `Prop` and irrelevant equality, full regularity breaks normalisation. TTobs/CCobs do not have definitional regularity (unverified against the papers). Regularity at inert types (CoreSpec §8.4) is Wiz's own; see D1. `--regularity full` restores the old rule for experiments. |
| Enumerations, `ecase`, equality of tags | **folklore** | Standard finite types. Labels are ignored (`Enum [a,b] ≡ Enum [c,d]`), which is harmless: a model can interpret `Enum` by its size. |
| Descriptions (`ret`, `arg`, `rec`, `hrec`), `Desc.elim`, `μ`, `ind` | **published** for levitated descriptions without quantities [CDMM10]; **conjecture** with quantities and with `Desc` as a primitive | The eliminator `Desc.elim` is large (into any `Sort v`). Field quantities and the quantity-polymorphic `marg` are Wiz's own. Fields live exactly in `Sort (l+1)`; smaller ones are lifted with `ULift` (F5, was Q4). |
| Observational equality at `μ` (`con x = con y ↦ x = y`, by the description) | **conjecture** | Natural, follows the TTobs pattern for inductive types; [PT22] treats ℕ and (unverified) general inductives differently. `μ D i ≡ μ D i'` (one family) computes to `i = i'`, other `μ ≡ μ` are stuck (CoreSpec §8.3). |
| Sized types: `Size`, `∞`, `↑`, `Size<`, subtyping, `sfix`, `scase` | **published** in outline [AVW17]; **conjecture** for Wiz's rules | Wiz's order and the D2 rule are its own (§10.1). Unfolding only on constructors follows Abel's MiniAgda (unverified). |
| Coinduction: `ν`, `out`, `cocon`, `coit`, `scofix` | **folklore** | Sized coinduction is Abel's; Wiz's exact rules have no paper. Equality at `ν` is stuck. |
| QTT usage accounting (the rig, scaling, subusaging) | **published** for Atkey's system [Atkey18] | Wiz differs: quantities are terms with polymorphism (§5.2), branches are joined (§5.3), eliminators scale methods by ω (Q2, fixed), projections on pairs (§7.1; Q1, fixed for `.2`), "σ = 1 everywhere, then discard" (§5.4). The differences are **conjecture**. |
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
| Observational equality + impredicative `Prop` + regularity | **resolved by D1 (a)**: regularity off; at inert types **conjecture** (argued, see D1) | D1, below. |
| Observational equality + descriptions (`eq` at `μ`, `cast` between `μ` types) | **conjecture** | `cast` between two `μ` types of one family computes on constructors (PT22/CIC-obs style, CoreSpec §8.4). Different parameters (`List A ≡ List B`) stay stuck. |
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
* **What remains.** Derived instances (`deriving`) for universe-polymorphic types are not
  supported (unrelated to Q4). The subject-reduction argument is on paper (CoreSpec §4.1,
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
  computes on data (CoreSpec §8.3, §8.4): `μ D i ≡ μ D i'` computes to `i = i'` and a
  cast between them casts each field of a constructor along the derived payload equation;
  `Desc` and `ν` likewise; equality at `μ` follows the description constructor by
  constructor, so `succ m = succ n` is `m = n` without a cast. The Abel–Coquand box now
  yields a stuck proof, and the program checks (tests "D1 (Abel–Coquand): the program
  checks …", "… the Wiz kernel checks the program …"; with `--regularity full`, resp.
  `kernelRegularity := .true`, both kernels still loop, which the tests also check).
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
    agree at inert types. Abel–Coquand needs a non-rigid type. This property matters
    because Wiz's strict evaluator reduces proofs (it forces `e` inside `cast`), and
    Pujet–Tabareau's decidability proof for CCobs deliberately never reduces proofs.

  All three assume the same property of the system without regularity, which is itself
  unproved for Wiz. That system already has two identity casts that inspect types: at
  `Enum` on any argument, and at `Sort`.

  **Found gap (incompleteness, not unsoundness).** The side condition is syntactic
  (`sameVal`), so algorithmic conversion is not a congruence and is not stable under
  substitution.
  * `cast (Fin (f p)) (Fin (f q)) e k` stays stuck for a variable `k`, although
    `Fin (f p) ≡ Fin (f q)` by irrelevance, while the reflexive cast reduces to `k`.
  * Two stuck casts that are convertible before a substitution stop being convertible
    after one of them becomes syntactically reflexive.

  `sameFamily?` has the same defect. The fix is to decide the side condition with
  conversion. Confirmed by a probe (the note, §10): `h p q p` is well typed, but its δβ-reduct is rejected, so subject reduction fails for the algorithmic typing.
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

### Q1. Projections drop linear components — **fixed for `.2`** (`212aebf`, both kernels); `.1` still drops the second component

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

**Fix** (`.2`): when the first field's quantity `q` doesn't allow zero uses, `p.2` counts
`p` as used ω times (only an unrestricted pair, whose field is `ω·q`, may drop it), so
`drop` above is rejected (both kernels; tests in "check: structural types" and the differential
samples). `p.1` still drops the second component: the second part of a Σ has no
quantity of its own, so the rule has nothing to check. Consume a linear pair with
`let 1 (x, y) := p`.

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

## 5. Stuck but sound

These are places where the kernel deliberately does **not** compute, so some true
equations are not provable by computation. They are incompleteness, not unsoundness.

* **Π/Σ without a sort annotation.** Type equality and `cast` need to know whether a type
  is a proposition (§8.3). Without an annotation the equation stays stuck. At `9717950`
  the elaborator leaves several internally built Π/Σ without one. The branch
  `agent/elab-sorts` (commit `31395a2`, not merged at `9717950`) annotates them using the
  kernel's `typeSort?`, except "a Π/Σ under a `fun` whose variable's type isn't written
  down, or one that still mentions a metavariable" (its README 4c text, now in [stages/04-data.md](stages/04-data.md)).
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
  and the kernel's own generated types, and everything after
  type checking (erasure, the backends).
* **Termination** of the kernel is not proved and is known to fail (D1); all evaluation
  functions are `partial` in Lean.
* **The evaluator reduces proofs.** `eval` is strict, and `vCast` forces `e` (through
  `vFst`/`vSnd`, and by applying `e.1`). So the kernel terminates only if the proofs it
  forces normalise. Pujet–Tabareau's decidability result for impredicative OTT (CCobs,
  POPL 2023) is proved *without* normalising proofs: in their words, the Abel–Coquand
  loop "is not a problem if we don't reduce irrelevant proofs" (Pujet, HoTTEST 2023). So
  even a Wiz version of their theorem would not cover this kernel as written. An
  evaluator that never forces proof positions would close that gap.
  (`/workspace/wiz-notes/inert-regularity.md` §2.)

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
| `partial def bad : T .f` + `boom : False` (O2) | accepted: `boom : False` |
| `partial def bad2 : False := bad2` (control) | rejected |
| `partial def bad : T .t → T .f` (O2) | accepted |
| wrong `builtin nat.add` (O3) | accepted: `bad : False` |
| `builtin nat := E` (empty) + `(0 : E)` (O3) | `wiz check` crashes (stack overflow) |
| `p.2` on a linear pair (Q1) | rejected since `212aebf` (was accepted) |
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
[PT22], [PT23], Agda #3026 (checked); [ML84], [AMS07], Gilbert et al. (not re-checked).
