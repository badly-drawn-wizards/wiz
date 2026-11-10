# The Wiz core: reference specification

This document states the calculus that Wiz's kernel checks, as inference rules, so that
someone who knows type theory can review it without reading the implementation first.
It is derived from the code, not from the stage docs ([stages/](stages/)). Where the two disagree, §14 lists the
disagreement. What is proved about the calculus, and what is not, is in
[Status.md](Status.md).

* **Kernel (reference):** `Wiz/Core/` (Lean 4). `Check.lean` (typing), `Conv.lean`
  (definitional equality, subtyping, sizes), `Eval.lean` (evaluation and the computation
  rules), `Level.lean` (universe levels), `QPoly.lean` and `Usage.lean` (quantities),
  `Templates.lean` (the generic operations on descriptions).
* **Mirror:** `selfhost/Kernel.wiz`, the same kernel written in Wiz. It covers a fragment
  (§15) and differs in places, listed per rule and in §15.
* **Line numbers** refer to the `solutions` branch at commit `9717950`. They drift as the
  code changes. The function names are the stable reference.

Each rule is tagged:

* **[std: X]**: the rule is the standard one from reference X (§16);
* **[wiz]**: the rule, or this form of it, is specific to Wiz. That does not make it
  wrong, but no published system checked by us contains it;
* **[impl]**: a rule that exists for the implementation only (glued evaluation, numerals),
  meant to be invisible in the theory.

"Unverified" marks a claim we did not check.

---

## Contents

1. [Reading guide](#1-reading-guide)
2. [Syntax](#2-syntax)
3. [Judgment forms](#3-judgment-forms)
4. [Universes and levels](#4-universes-and-levels) (4.1 [Lifting](#41-lifting-ulift-q4))
5. [Quantities](#5-quantities)
6. [Variables, Π, λ, application, let](#6-variables-π-λ-application-let)
7. [Σ, Unit, Empty, True, False, enumerations](#7-σ-unit-empty-true-false-enumerations)
8. [Observational equality](#8-observational-equality)
9. [Descriptions, μ and induction](#9-descriptions-μ-and-induction)
10. [Sizes, ν and sized (co)recursion](#10-sizes-ν-and-sized-corecursion)
11. [Definitional equality and subtyping](#11-definitional-equality-and-subtyping)
12. [Evaluation strategy](#12-evaluation-strategy)
13. [Global declarations and universe polymorphism](#13-global-declarations-and-universe-polymorphism)
14. [Where the code and the stage docs disagree](#14-where-the-code-and-the-stage-docs-disagree)
15. [The self-hosted kernel (`Kernel.wiz`)](#15-the-self-hosted-kernel-kernelwiz)
16. [What is not in the core, and who checks what](#16-what-is-not-in-the-core-and-who-checks-what)
17. [References](#17-references)

---

## 1. Reading guide

The kernel is a **bidirectional type checker with normalisation by evaluation (NbE)**.
Terms use de Bruijn indices. Types are evaluated into a semantic domain of values
(closures, neutrals), and definitional equality is decided on values, directed by their
type. In the rules below, a substitution such as `B[a/x]` is what the kernel computes by
instantiating a closure (`Closure.inst`, `Eval.lean:282`). `≡` is the conversion
algorithm of §11, and `≤` is subtyping (§11.5).

Three features make Wiz's core unusual, and they interact everywhere:

1. **Quantities (QTT).** Every binder carries a quantity from a rig, and every judgment
   also outputs a *usage vector*: how often the term uses each variable at run time.
2. **Observational equality (OTT).** `a = b` is not an inductive type. It is a proposition
   that computes by the type of `a`, and `cast` computes by the two types. Propositions are
   definitionally proof-irrelevant, and `Prop` is impredicative.
3. **Anonymous data.** Inductive and coinductive types are `μ D i` / `ν D i` for a
   *description* `D` (a first-class value), with **sizes** on both.

---

## 2. Syntax

`Wiz/Core/Term.lean:41–159`. Binders are written with names here, for readability.

```
q, r     ::= qlit ρ   (ρ ∈ R, the rig)   |  x  (a variable of type Qty)        quantities
l, u     ::= 0 | l+1 | max l u | imax l u | ν   (ν a level parameter)          levels
s        ::= ∞ | ↑s | x                                                      sizes (terms of type Size)

t, A, B ::=
  x | c.{l…}                                      variables, global constants
  Sort l                                          universes (Prop = Sort 0, Type u = Sort (u+1))
  (q x : A) → B  [σ]                              Π, optional sort annotation σ (a level)
  λx. t | t u                                     no domain or quantity on λ
  let x :q A := t; u | (t : A)                    let, ascription
  (q x : A) × B  [σ] | (t, u) | t.1 | t.2         Σ (optional sort annotation σ)
  let q (x, y) := t as z. M; u                    Σ elimination (`split`)
  Unit_l | tt | Empty_l | absurd M t              Unit_0 = True, Empty_0 = False
  ULift.{l} A | up t | down t                     lifting to a bigger universe (§4.1, Q4)
  t = u   (written eq A t u)                      observational equality of elements
  A ≡ B   (written eqTy A B)                      equality of types
  refl A t | reflTy A | cast A B e t | transp A a P p b e
  Qty | qlit ρ                                    the type of quantities, literals
  Enum [ℓ₀…ℓₙ₋₁] | tag k | ecase t as z. M [b₀…bₙ₋₁]   (labels ℓ are metadata)
  Desc.{l} I | ret i | arg q S D | rec q j D | hrec q H j D
  Desc.elim.{v} P mret marg mrec mhrec D
  μ.{l} I D i ^s | con t | ind.{l,v} I D P m i t
  ν.{l} I D i ^s | out t | cocon t | coit.{l} I D S step i t
  Size | ∞ | ↑s | Size< s
  sfix.{l,v} I D P f s i t | scase.{l,v} I D P m s i t | scofix.{l} I D A f s i a
  n  (natLit)                                     numerals of the type registered by `builtin nat`
  ?m (mvar)                                       elaborator only: the kernel rejects it
```

`natOp` (`Term.lean:158`) is produced only by evaluation and never type-checked. `μ` and `ν`
also carry a *display hint* (the nominal name to print) that conversion ignores.
`BinderInfo` (explicit/implicit) is ignored by the kernel.

---

## 3. Judgment forms

```
Γ ⊢ t ⇒ A ⊣ U        infer:  t synthesises type A, using the variables of Γ as U       (Check.lean:338)
Γ ⊢ t ⇐ A ⊣ U        check:  t checks against A, using U                              (Check.lean:256)
Γ ⊢ A type@l         A ⇒ Sort l, checked in erased mode, usage discarded             (checkType, Check.lean:660)
Γ ⊢ q qty ↦ p        q ⇐ Qty, and its value is the quantity polynomial p             (checkQty, Check.lean:654)
Γ ⊢ a ≡ b : A        conversion (decided)                                            (conv, Conv.lean:252)
Γ ⊢ A ≡ B type       type conversion                                                 (convTy, Conv.lean:326)
Γ ⊢ A ≤ B            subtyping (sizes)                                               (subTy, Conv.lean:474)
Γ ⊢ s ≤ s'  /  Γ ⊢ s < s'   size order                                              (sizeLe, sizeBelow, Conv.lean:126, 143)
⊢ l ≡ l'             level equivalence                                               (Level.equiv, Level.lean:291)
```

**Contexts** (`Ctx`, `Check.lean:169`): a list of entries `x :p A` (a quantity polynomial
`p` and a type value `A`) or `x :p A := v` (a `let`), together with a flag `erased`
(written `Γ⁰` when set). Index 0 is the innermost entry.

**Usage vectors** `U` (`Usage.lean`) have one quantity polynomial per context entry. `0ₙ`
is the zero vector, `𝟙ₓ` is "x used once" (`Usage.single`), `U + V` is pointwise sum,
`p·U` is pointwise scaling. The rules below write `⊣ 0` for `⊣ 0ₙ`.

**Erased mode** `Γ⁰` is a light version of Atkey's σ = 0 (§5.4). It is switched on for
type positions, arguments to `0`-quantity binders, proofs and sizes, and its only effect is
to allow projecting an erased field (rule *fst*).

---

## 4. Universes and levels

`Level.lean`. Levels are Lean 4's: `0`, `l+1`, `max`, `imax`, parameters, and level
metavariables (elaborator only).

```
                                  ─────────────────────────── sort        [std: CIC/Lean]   Check.lean:353
                                  Γ ⊢ Sort l ⇒ Sort (l+1) ⊣ 0
```

* **Non-cumulative.** There is no rule `Sort l ≤ Sort (l+1)`; `Type 0 : Type 1` only.
  (`subTy`, `Conv.lean:474`, has no universe case.) Cumulativity is optional exercise 1.11.
* **Impredicative `Prop`.** Π takes `imax` (rule *pi*, §6), so `(x : A) → P` is in `Prop`
  whenever `P` is, whatever `A`'s universe. [std: CIC/Lean]
* **Level equivalence** `⊢ l ≡ l'` (`Level.equiv`, `Level.lean:291`): both sides are
  normalised to a sorted list of `(atom, offset)` meaning their `max`
  (`normalize`, `Level.lean:265`); an `imax a b` whose `b` is not visibly nonzero stays
  an atom. If the normal forms differ, the algorithm case-splits on a parameter that
  decides some `imax` (`p = 0` or `p = p'+1`), with fuel 8. This is sound (equal answers
  hold under every instantiation of the parameters) and complete without `imax`; with
  `imax` it is incomplete, as in Lean. [std: Lean 4 kernel; the comment in `Level.lean`
  says so; not checked against Lean's source]
* `l ≤ l'` is `max l l' ≡ l'` (`Level.le`, `Level.lean:301`). `isNeverZero l`
  (`Level.lean:278`) means some entry of the normal form has offset ≥ 1.

Level metavariables never reach the kernel in a checked declaration (the elaborator
solves or defaults them). The kernel does not reject them explicitly; it treats them as
opaque atoms.

### 4.1 Lifting: `ULift` (Q4)

Universes are not cumulative, so a type in a small universe is moved up explicitly.
`ULift.{l} A` (`Term.ulift`) is a copy of `A : Sort k` in `Sort l`, for `k ≤ l`. Its only
use in the core is in descriptions: a description field must be in exactly `Sort (l+1)`
(§9.1), and the elaborator wraps smaller fields. [std: Agda's `Lift`, Lean's `ULift`;
the levitated descriptions of [CDMM10] fix the field level and use `Lift` the same way]

```
     Γ ⊢ A type@k    k ≤ l                Γ ⊢ a ⇐ A ⊣ U                 Γ ⊢ t ⇒ ULift.{l} A ⊣ U
     ─────────────────────── ulift        ──────────────────── up        ─────────────────────── down
     Γ ⊢ ULift.{l} A ⇒ Sort l ⊣ 0         Γ ⊢ up a ⇐ ULift.{l} A ⊣ U     Γ ⊢ down t ⇒ A ⊣ U

     down (up a) ⟶ a                                                       (β)      vDown, Eval.lean
     t ≡ t' : ULift A   iff   down t ≡ down t' : A                         (η)      conv, Conv.lean
     ULift.{l} A ≡ ULift.{l'} A'   iff   l ≡ l' and A ≡ A'                           convTy
```

`up` is checked only (its type can't be inferred). `down` is an elimination: it is stuck on
a neutral and quotes back as `down t`. Usages pass through (`up a` and `down t` use what `a`
and `t` use).

**Propositions.** `ULift.{l} P` for a proposition `P` is a proposition only when `l ≡ 0`
(then `P : Sort 0`, and `ULift.{0} P` is equivalent to `P`). For `l` never `0` it is not a
proposition: its inhabitants are **boxed proofs**. They are not all convertible by proof
irrelevance at their own type (`typeSort? (ULift.{l} P) = l`), but they are by η, since
`down t ≡ down t' : P` by proof irrelevance at `P`. So a lifted proposition has one
inhabitant up to conversion, like `Unit`. Whether a type is a proposition stays a property of
the type itself (its sort, `propSort?`), never of the sort it is used at.

**Observational equality** (`vEq`, `vEqType`, `vCast`; the given lines at the top of each):

```
a =_{ULift.{l} A} b    ⟶  True                         if A is a proposition (propSort? A = true)
                       ⟶  down a =_A down b            if A is not one (propSort? A = false)
                       ⟶  stuck                        if unknown
ULift.{u} A ≡ ULift.{w} B ⟶  (X → Y) × (Y → X)         if both are propositions (u ≡ w ≡ 0)
                       ⟶  A ≡ B                        if u ≡ w
                       ⟶  False                        if u, w are closed and different; else stuck
ULift A ≡ B, B another canonical former  ⟶  False      (ULift is in `canonical`: no confusion)
cast (ULift.{u} A) (ULift.{w} B) e t
                       ⟶  up (cast A B e (down t))     if u ≡ w and u is never 0
                       ⟶  e.1 t                        if both are propositions
                       ⟶  stuck                        otherwise
```

These follow the pattern of the other formers [std: PT22's rules for a type former with
one constructor]: the code equation is injective (`ULift A ≡ ULift B` iff `A ≡ B`) and
the cast goes through the eliminator. They agree with the casts on data (§8.4, D1): the
payload cast of a constructor casts each field, and a lifted field `up x` is cast to
`up (cast S S' ê₁ x)`, so a lifted proof field becomes the equivalence applied to the
proof (a stuck proof), exactly as an unlifted proof field did: the D1 argument (no proof
returned unchanged) still holds. `ULift A` is inert when `A` is (`inertTy`), and a lifted
proposition is not. The rule for `cast` requires `u` never `0` (not merely "not known to
be 0"), so the choice between the two rules is stable under level substitution.

**Subject reduction for the new rules.** *β*: `down (up a)` has type `A` because `up a ⇐
ULift A` needs `a ⇐ A`. *η* only adds conversions between terms of the same type.
*`vEq`*: `a =_{ULift A} b` is formed when `ULift A` is in a never-zero sort, and `down a`,
`down b : A`, so `down a =_A down b` is a well-formed proposition when `A` is not a
proposition; when `A` is one, the equation is about boxed proofs, which are all equal
(η + irrelevance), so `True` is its value. *`vEqType`*: `ULift.{l} A ≡ ULift.{l} B` is
formed at one level `l`; `A ≡ B` may relate types at different levels `k, k' ≤ l`, which
`eqTy` would not form directly, but (as with the Π/Σ decomposition, §8.3) it then
computes to `False` or stays stuck: the levels of `A` and `B` are visible in their
shapes. *`vCast`*: with `e : ULift A ≡ ULift B`, which computes to `A ≡ B`, `cast A B e
(down t) : B` and `up` of it is a `ULift B`.

**Erasure.** `ULift` has no runtime content: `up a` erases to `a`, `down t` to `t`, and
`ULift A` is erasable exactly when `A` is (a lifted proof is still erased). A description
whose tag is lifted (`arg q (ULift (Enum ls)) F`) is still marked as starting with a tag.
So lifting changes no runtime representation (`#ir` is unchanged). A field of an
infinitary constructor with a lifted domain is read as `fun h => f (up h)`, which erases to
`f` (an η-step in `eraseCheck`).

---

## 5. Quantities

### 5.1 The rig

`Wiz/Rig.lean`. A `QRig` is a commutative semiring `(R, +, 0, ·, 1)` with a decidable
preorder `le used declared`, monotone in `+` and `·` (the laws are fields of the class, so
every instance carries their proofs). The kernel is parametric in `R`. The `wiz` command
line and the test suite use `ZeroOneMany = {0, 1, ω}` (`Wiz/Rig/Instances.lean:76`,
`Main.lean:48`):

```
+ : 0+a = a,  1+1 = 1+ω = ω+ω = ω          · : 0·a = 0,  1·a = a,  ω·ω = ω
le used declared  ⇔  used = declared  ∨  declared = ω                     (so 0 ≤ 1 is FALSE: 1 is linear)
```

Other instances: `Unit` (plain MLTT) and `Nat` (exact counting, `le` is `=`). Each rig also
fixes a default quantity for binders the kernel generates itself, `explicitDefault`
(`ω` for `ZeroOneMany`, `1` for `Nat`, `()` for `Unit`).

### 5.2 Quantity terms and polynomials

Quantities are terms of type `Qty` (stage 4d). `Qty : Sort 1`, `qlit ρ : Qty`. A binder's
quantity is evaluated to a **polynomial** over the rig whose variables are `Qty`-typed
locals (`QPoly.lean`); anything else (a stuck computation) is rejected (`qtyPoly`,
`Check.lean:223`).

```
     Γ⁰ ⊢ q ⇐ Qty     eval q = p polynomial
     ──────────────────────────────────────── qty         [wiz]   checkQty, Check.lean:654
     Γ ⊢ q qty ↦ p

     ───────────────────── Qty                ───────────────────── qlit                    Check.lean:485–486
     Γ ⊢ Qty ⇒ Sort 1 ⊣ 0                     Γ ⊢ qlit ρ ⇒ Qty ⊣ 0
```

`p ≤ p'` (`QPoly.le`, `QPoly.lean:88`) is `le` on constants; on polynomials with variables
it must hold under **every** assignment of the variables to rig elements, which needs a
finite rig (`elements?`); for an infinite rig only syntactically equal polynomials are
related (`leSymbolic`, `QPoly.lean:75`). Note that `checkQty`'s usage is discarded and its
check is **not** in erased mode (`Check.lean:655`); a quantity is a type-level object, so
this is harmless.

### 5.3 Usage accounting

The judgments output usage vectors with these operations [std: Atkey18; McBride16]:

* **variables** use themselves once: `𝟙ₓ`;
* **application** to a `q`-binder scales the argument's usage by `q`: `U₁ + q·U₂`;
* **leaving a binder** declared `q` pops its usage `u` and requires `u ≤ q`
  (**subusaging**, `popUsage`, `Check.lean:231`);
* **types, quantities and proofs use nothing** (their usage is discarded);
* **branches** of an `ecase` combine by the **join** `⊔` (least upper bound in `≤`) of
  their usages (`QPoly.join?`, `QPoly.lean:105`); `0 ⊔ 1 = ω` in `{0,1,ω}`, and if
  there is no join the case is rejected [wiz: Atkey's QTT has no case analysis on
  enumerations of this form; booleans in Atkey18 require both branches to use the same
  context, which is the `1 ⊔ 1 = 1` instance];
* **eliminators that run a method once per node** (`ind`, `Desc.elim`, `sfix`, `scofix`,
  `coit`) scale the method's usage by the rig's unrestricted quantity `QRig.many?` (ω);
  a rig without one (exact counting, `Nat`) rejects methods that use local variables
  outside erased positions (`methodUsage`) (§9, §10) [wiz]. (Before `a986c02` the scale
  was `explicitDefault`, which under-counted in the `Nat` rig: Status.md, Q2.)

### 5.4 Erased mode, versus Atkey's σ

Atkey's system has judgments at σ ∈ {0, 1} and does not track usage at σ = 0. Wiz checks
everything in the σ = 1 style and then discards the usage of type positions
(`checkType`, `Check.lean:660`) and of arguments to `0`-binders (scaled by 0). The
module docstring (`Check.lean:131–137`) says this "is sound but rejects a few erased terms
that Atkey would accept". The `erased` flag (`Ctx.erased`, `Check.lean:180`) restores one
of them: projecting an erased Σ field. Whether this simplification is sound in Atkey's
sense is **unverified** (it is plausible: it only rejects more, and discarding usage is
what the 0-fragment does anyway).

---

## 6. Variables, Π, λ, application, let

```
     ─────────────────────────────── var            [std]            Check.lean:346
     Γ ⊢ x ⇒ Γ(x) ⊣ 𝟙ₓ

     Γ ⊢ q qty ↦ p    Γ ⊢ A type@i    Γ, x :p A ⊢ B type@j    (σ given ⇒ ⊢ σ ≡ imax i j)
     ──────────────────────────────────────────────────────────────── pi      Check.lean:354–359
     Γ ⊢ (q x : A) → B [σ] ⇒ Sort (imax i j) ⊣ 0
```
[std: Atkey18 for the quantity, Lean for `imax`; the sort annotation σ is [wiz], checked by
`checkSortNote`, `Check.lean:243`. Its purpose is §8.3.]

```
     Γ, x :p A ⊢ b ⇐ B ⊣ (u :: U)     u ≤ p         (p = value of q)
     ──────────────────────────────────────────── lam     [std: Atkey18]    Check.lean:259–262
     Γ ⊢ λx. b ⇐ (q x : A) → B ⊣ U

     Γ ⊢ f ⇒ T ⊣ U₁     whnf T = (q x : A) → B     p = value of q
     Γ' ⊢ a ⇐ A ⊣ U₂    where Γ' = Γ⁰ if p is the constant 0, else Γ
     ──────────────────────────────────────────── app     [std: Atkey18]    Check.lean:368–375
     Γ ⊢ f a ⇒ B[a/x] ⊣ U₁ + p·U₂

     Γ ⊢ q qty ↦ p   Γ ⊢ T type@_   Γ ⊢ v ⇐ T ⊣ U₁   Γ, x :p T := v ⊢ b ⇐ A ⊣ (u :: U₂)   u ≤ p
     ──────────────────────────────────────────── let (⇐; the ⇒ form is the same)    Check.lean:263–270, 376–383
     Γ ⊢ let x :q T := v; b ⇐ A ⊣ p·U₁ + U₂

     Γ ⊢ T type@_     Γ ⊢ t ⇐ T ⊣ U
     ──────────────────────────────── ann                       Check.lean:384–388
     Γ ⊢ (t : T) ⇒ T ⊣ U

     Γ ⊢ t ⇒ A' ⊣ U     Γ ⊢ A' ≤ A
     ──────────────────────────────── switch (subsumption)      Check.lean:311–315
     Γ ⊢ t ⇐ A ⊣ U
```

`λ` cannot be inferred (`Check.lean:366`). `let` is transparent: the body sees
`x := v` (`Ctx.define`, `Check.lean:196`), so `x` unfolds during conversion. The switch rule
uses **subtyping**, not conversion; subtyping differs from conversion only on sizes (§11.5).

*Kernel.wiz.* `app` evaluates the argument only if the codomain may mention it
(`usesVar`, `Kernel.wiz:1719`, a conservative syntactic test; `Kernel.wiz:1772–1782`).
The `lam` rule is `Kernel.wiz:2116`. Quantities are the three literals only.

---

## 7. Σ, Unit, Empty, True, False, enumerations

### 7.1 Σ

```
     Γ ⊢ q qty ↦ p   Γ ⊢ A type@i   Γ, x :p A ⊢ B type@j   (σ given ⇒ ⊢ σ ≡ max i j)
     ──────────────────────────────────────────────────────── sigma               Check.lean:389–394
     Γ ⊢ (q x : A) × B [σ] ⇒ Sort (max i j) ⊣ 0

     Γ ⊢ a ⇐ A ⊣ U₁     Γ ⊢ b ⇐ B[a/x] ⊣ U₂
     ──────────────────────────────────────── pair  (check only)                  Check.lean:271–275
     Γ ⊢ (a, b) ⇐ (q x : A) × B ⊣ p·U₁ + U₂

     Γ ⊢ t ⇒ T ⊣ U    whnf T = (q x : A) × B    (1 ≤ p  or  Γ is Γ⁰)
     ──────────────────────────────────────── fst                                  Check.lean:395–403
     Γ ⊢ t.1 ⇒ A ⊣ U

     Γ ⊢ t ⇒ T ⊣ U    whnf T = (q x : A) × B
     ──────────────────────────────────────── snd                                  Check.lean:404–408
     Γ ⊢ t.2 ⇒ B[t.1/x] ⊣ U

     Γ ⊢ r qty ↦ ρ     Γ ⊢ s ⇒ T ⊣ U₁     whnf T = (q x : A) × B   (p = value of q)
     Γ, z :0 T ⊢ M type@_
     Γ, x :ρ·p A, y :ρ B ⊢ b ⇐ M[(x,y)/z] ⊣ (u_y :: u_x :: U₂)     u_y ≤ ρ    u_x ≤ ρ·p
     ──────────────────────────────────────── split                               Check.lean:409–424
     Γ ⊢ let r (x, y) := s as z. M; b ⇒ M[s/z] ⊣ ρ·U₁ + U₂
```

* Σ with `split` is Atkey's dependent tensor ⊗ [std: Atkey18]. η for pairs holds
  (§11.2).
* **Projections are [wiz].** Atkey's tensor has only the `let` eliminator. Wiz also allows
  `t.1` (when the field's quantity allows one use) and `t.2` (always; since `212aebf`, if the field
  doesn't allow zero uses, `t.2` uses `t` ω times, so only an unrestricted pair may drop
  it). Each projection uses the whole pair, so using both on a
  linear pair is rejected. `p.1` still silently drops the second component, which has no
  quantity of its own. (Before `212aebf`, `p.2` on `(1 x : A) × B` discarded the linear
  `x`.) This is consistent with an *affine* reading of `1`, not with "exactly once"
  (the rig's stated meaning, `Rig.lean:22–24`). It cannot affect logical consistency or
  erasure (a dropped value is never needed), but it is a gap in the linearity guarantee.
  See Status.md, Q1.
* `split`'s motive variable `z` has quantity 0 (`ctx.bind z []`, `Check.lean:415`).
* The sort annotation `σ` is not checked for `split`'s scrutinee; it is checked where the
  Σ type is formed.

*Kernel.wiz* has no `split` (no `let (x, y)` in its term syntax, `Kernel.wiz:40–119`).
Its `fst` rule is `Kernel.wiz:1791`.

### 7.2 Unit, Empty, True, False

`Unit_l` and `Empty_l` exist at every level; `True = Unit_0`, `False = Empty_0`.

```
     ─────────────────────── unit    ───────────────────── tt (check only)   ──────────────────────── empty
     Γ ⊢ Unit_l ⇒ Sort l ⊣ 0         Γ ⊢ tt ⇐ Unit_l ⊣ 0                    Γ ⊢ Empty_l ⇒ Sort l ⊣ 0
                                                                                  Check.lean:425–426, 276

     Γ ⊢ M type@_      Γ⁰ ⊢ t ⇒ T     whnf T = Empty_l
     ──────────────────────────────────────── absurd                                Check.lean:427–433
     Γ ⊢ absurd M t ⇒ M ⊣ 0
```

η for Unit: all elements of `Unit_l` are definitionally equal (§11.2). `absurd` never
computes (`vAbsurd`, `Eval.lean:84`). Its usage is **0**: `t` is checked in erased mode
and its usage discarded [wiz; see §14, the docstring says `⊣ U`].

### 7.3 Enumerations

```
     ───────────────────────── enum     i < n
     Γ ⊢ Enum ls ⇒ Sort 1 ⊣ 0           ─────────────────────────── tag                     Check.lean:491–494
                                        Γ ⊢ tag ls i ⇒ Enum ls ⊣ 0      (n = |ls|)

     Γ ⊢ t ⇒ T ⊣ U    whnf T = Enum ls    |bs| = |ls|    Γ, z :0 Enum ls ⊢ M type@_
     Γ ⊢ bₖ ⇐ M[tag k/z] ⊣ Vₖ   (each k)      V = V₀ ⊔ … ⊔ Vₙ₋₁  (defined)
     ──────────────────────────────────────── ecase                                  Check.lean:495–510
     Γ ⊢ ecase t as z. M [b₀…] ⇒ M[t/z] ⊣ U + V

     ecase (tag k) as z. M [b…]  ⟶  bₖ                                              vEcase, Eval.lean:335
```

[std for finite types; the join of branch usages is wiz, §5.3]. **Labels are metadata**:
`Enum [a, b]` and `Enum [c, d]` are convertible (`Conv.lean:342`) and equal
(`Eval.lean:592`); only the number of tags matters. `ecase` on an empty enumeration has
no branches and usage `U`.

---

## 8. Observational equality

Stage 4c. This section follows Pujet and Tabareau's TTobs [PT22] and the earlier OTT
[AMS07] in outline. Wiz-specific parts are marked.

### 8.1 Typing

```
     Γ ⊢ A type@l    isNeverZero l    Γ ⊢ a ⇐ A    Γ ⊢ b ⇐ A
     ──────────────────────────────────────── eq                                    Check.lean:435–442
     Γ ⊢ a =_A b ⇒ Prop ⊣ 0

     Γ ⊢ A type@l    Γ ⊢ B type@l'    ⊢ l ≡ l'
     ──────────────────────────────────────── eqTy                                  Check.lean:443–447
     Γ ⊢ A ≡ B ⇒ Prop ⊣ 0

     Γ ⊢ A type@l    isNeverZero l    Γ ⊢ a ⇐ A                Γ ⊢ X type@_
     ───────────────────────────────────── refl                 ─────────────────────────── reflTy
     Γ ⊢ refl A a ⇒ (a =_A a) ⊣ 0                               Γ ⊢ reflTy X ⇒ (X ≡ X) ⊣ 0
                                                                       Check.lean:448–457

     Γ ⊢ A type@l   Γ ⊢ B type@l'   ⊢ l ≡ l'   Γ⁰ ⊢ e ⇐ (A ≡ B)   Γ ⊢ t ⇐ A ⊣ U
     ──────────────────────────────────────── cast                                  Check.lean:458–466
     Γ ⊢ cast A B e t ⇒ B ⊣ U

     (all premises in Γ⁰)  Γ⁰ ⊢ A type@_   Γ⁰ ⊢ a ⇐ A   Γ⁰ ⊢ b ⇐ A
     Γ⁰ ⊢ P ⇐ (b :0 A) → (_ :0 a =_A b) → Prop
     Γ⁰ ⊢ p ⇐ P a (refl A a)    Γ⁰ ⊢ e ⇐ (a =_A b)
     ──────────────────────────────────────── transp                                Check.lean:467–484
     Γ ⊢ transp A a P p b e ⇒ P b e ⊣ 0
```

* `a = b` is only formed at a type whose sort is **never** `Prop` (`isNeverZero`).
  Equality of proofs is not expressible, which is consistent with proof irrelevance.
* The written type `A` of `eq` and `refl` is not tied to `a`'s type by anything other than
  `a ⇐ A`.
* `cast` is the only operation whose *result* is relevant; `transp` (transport into a
  `Prop`-valued family) is a proof. Together they give J (`examples/equality.wiz`).
  [std: PT22]
* Proofs have no usage (`⊣ 0`) and **never compute**: `refl`, `reflTy` and `transp`
  evaluate to stuck neutral heads (`Eval.lean:157–161`). Only `cast` computes.

### 8.2 Computation of `a =_A b`

`vEq`, `Eval.lean:514–549`, by the weak head normal form of `A`:

| `A` | `a =_A b` reduces to | tag | line |
|---|---|---|---|
| `(q x : A₁) → B` | `(0 x : A₁) → a x =_{B x} b x` (funext) | [std: PT22] | 523–525 |
| `(q x : A₁) × B` | `(0 e : a.1 =_{A₁} b.1) × (cast (B a.1) (B b.1) ê a.2 =_{B b.1} b.2)`, where `ê = transp A₁ a.1 (λy _. B a.1 ≡ B y) (reflTy (B a.1)) b.1 e` | [std: PT22] | 526–532 |
| `Unit_l`, `Empty_l` | `True` | [std] | 533 |
| `Enum ls`, with `a = tag i`, `b = tag j` | `True` if `i = j`, else `False` | [wiz: finite types] | 534–536 |
| `μ D i`, with `a = con x`, `b = con y` | `x =_{⟦D⟧ (μ D) i} y`, **by the description** (`vEqPayload`, below) | [wiz: OTT for descriptions] | `vEqPayload` |
| `Sort l`, `l ≡ 0` | `(a → b) × (b → a)` (**propext**) | [std: PT22] | 540–543 |
| `Sort l`, `isNeverZero l` | `a ≡ b` (type equality, §8.3) | [std: PT22] | 544 |
| `ULift A` | `True` if `A` is a proposition; `down a =_A down b` if it is not; else stuck | [std; Q4] | §4.1 |
| anything else (a neutral type, `ν`, `Sort u` with `u` possibly 0, a non-constructor element of `μ`/`Enum`) | stuck: the neutral `a =_A b` | | 545–546 |
| numerals `n`, `m` (any `A`) | `True` if `n = m`, else `False` | [impl] | 516 |

Equality of payloads by the description (`vEqPayload`), so that `succ m = succ n` is
`m = n` and not, through the Σ rule, an equation with a cast along the tags'
equation (which, without regularity, would be stuck at the field's type):

```
x = y  at ⟦ret j⟧ X i         ⟶  True                      (the payload is an index proof and ())
x = y  at ⟦arg q (Enum ls) E⟧ ⟶  x.1, y.1 both tags: equal ⟶ x.2 = y.2 at ⟦E tag⟧
       (or ULift (Enum ls): the tags are down x.1, down y.1, and E gets up tag)
                                                      different ⟶ the Σ rule (first component False)
                                 not both tags ⟶ the whole equation a =_μ b is stuck
x = y  at ⟦arg q S E⟧, S not an Enum  ⟶  the Σ rule
x = y  at ⟦rec q j E⟧          ⟶  (x.1 =_{X j} y.1) × (x.2 = y.2 at ⟦E⟧), or just x.1 = y.1 if E is ret
x = y  at ⟦hrec q H j E⟧       ⟶  (x.1 =_{(h:H) → X (j h)} y.1) × (x.2 = y.2 at ⟦E⟧), likewise
neutral D                      ⟶  stuck
```

Which rule applies depends only on `D` and on whether the tags are canonical, and the
alternative to computing is being stuck (whose quotation is the original equation), so
the result is stable under substitution. The `rec`/`hrec` pairs are non-dependent, since
`E` does not depend on a recursive field. Dropping the `ret` leaf's `True` (and the equal
tags' `True`) makes the nesting independent of how a number is written: `succ^k zero =
succ^k zero` computes to `True`, as the numerals `k = k` do, and `0 = .zero` (a numeral
against a constructor, seen through `vNatView`) gives the same `True`.

Equality at `ν` stays stuck (no bisimulation): a design decision (4d, [stages/04-data.md](stages/04-data.md)). All
binders generated by these rules have quantity 0, and the generated Π/Σ carry the sort
annotation `0` (`some 0`), which is correct because each is built from propositions.

### 8.3 Computation of `A ≡ B` (type equality)

`vEqType`, `Eval.lean:563–597`. First the **proposition test** [wiz]:

```
propSort?(T) (Eval.lean:98–103) =
  Π/Σ with annotation σ:  true if σ ≡ 0, false if isNeverZero σ, else unknown
  Unit_l, Empty_l, ULift.{l} A:   true if l ≡ 0, false if isNeverZero l, else unknown
  Sort, Qty, Enum, Desc, μ, ν, Size, Size<:   false
  a stuck eq / eqTy (empty spine):   true
  anything else (neutral, Π/Σ with no annotation):   unknown
```

Then:

```
both true                         ⟶  (X → Y) × (Y → X)          propositions are equal when equivalent
either unknown                    ⟶  stuck
one true, one false               ⟶  False
both false, by shape:
  ((q x:A)→B) ≡ ((q' x:A')→B')    ⟶  False if q, q' are different constants (both closed: F6);
                                     stuck if either has a variable and they are not equivalent;
                                     else (0 e : A' ≡ A) × ((0 x : A') → B (cast A' A e x) ≡ B' x)
  ((q x:A)×B) ≡ ((q' x:A')×B')    ⟶  (same quantity test)  (0 e : A ≡ A') × ((0 x : A) → B x ≡ B' (cast A A' e x))
  Sort u ≡ Sort w, Unit_u ≡ Unit_w, Empty_u ≡ Empty_w
                                  ⟶  True if u ≡ w; False if both closed and different; else stuck
  Enum ls ≡ Enum ls'              ⟶  True if |ls| = |ls'|, else False
  Desc_l I ≡ Desc_l' I'          ⟶  I ≡ I' if l ≡ l', else stuck                          [wiz]
  ULift.{u} A ≡ ULift.{w} B      ⟶  A ≡ B if u ≡ w; False if both closed and different; else stuck   [Q4, §4.1]
  μ^s_l I D i ≡ μ^s'_l' I' D' i'  ⟶  i =_I i' if l ≡ l' and s, I, D are syntactically equal  [wiz, D1]
  (the same for ν)                    to s', I', D' (quoted, as `sameVal`); else stuck
  two different canonical formers (Π, Σ, Sort, Unit, Empty, Enum, Desc, μ, ν, ULift)
                                  ⟶  False                        (no-confusion of type formers)
  otherwise                       ⟶  stuck
```

* **The quantity test** must be stable under substitution. `False` needs two *closed*
  quantities. A variable `q` and `1` are different polynomials, but `q := 1` makes them
  equal. Deciding `False` there proved `False` (Status.md, F6).
* The Π/Σ decomposition and "different formers ⇒ False" are TTobs's [std: PT22]. The
  Π case puts the domain equation backwards (`A' ≡ A`), as in PT22 (unverified detail).
* **Propositions compared by equivalence, and the sort annotation** are [wiz]. They exist
  because comparing propositions by shape proved `False` (Status.md, issue F1). A Π or Σ
  can't tell by its parts alone whether it is a proposition, so it carries its sort `σ`,
  which the kernel checks when the type is formed (rule *pi*, *sigma*). A Π/Σ **without**
  an annotation makes type equality *stuck*. That is sound (stuck terms prove nothing) but
  incomplete (Status.md, "stuck but sound").
* **Quantities are part of a type's identity**: `(1 x : A) → B ≡ (ω x : A) → B` is
  `False` [wiz]. Conversion agrees (§11.3), except at propositions.
* `Size ≡ Size`, `Size< s ≡ Size< t`, `Qty ≡ Qty` are **stuck** in the Lean kernel
  (`Size`, `Size<` and `Qty` are not in `canonical`, `Eval.lean:572`). In `Kernel.wiz` they
  reduce to `False` (§15, and Status.md: this is a proof of `False` in the self-hosted
  kernel).
* Different universes: `eqTy` requires equal levels, but the Π/Σ decomposition can
  compare domains at different levels (e.g. `Nat ≡ True` from `(x : Nat) → Unit ≡
  (x : True) → Unit`). Then the proposition test answers `False`, and two non-propositional
  types at different levels are compared by shape (`Sort 0 ≡ Sort 1` is `False`).

### 8.4 Computation of `cast`

`vCast`, `Eval.lean:610–638`. With `A`, `B` in whnf:

```
propSort? A = propSort? B = true   ⟶  e.1 t                          (apply the equivalence)        617   [wiz]
Π/Π, quantities equal              ⟶  λx. cast (B₁ x̂) (B₂ x) (e.2 x) (t x̂),  x̂ = cast A₂ A₁ e.1 x  619–624 [std: PT22]
Π/Π or Σ/Σ, quantities not known equal ⟶  stuck
Σ/Σ, quantities equal              ⟶  (c₁, cast (B₁ t.1) (B₂ c₁) (e.2 t.1) t.2),  c₁ = cast A₁ A₂ e.1 t.1   625–629 [std: PT22]
Sort u/Sort w, Empty_u/Empty_w     ⟶  t if u ≡ w, else stuck                                         630
Unit_u/Unit_w                      ⟶  tt if u ≡ w, else stuck                                        631
Enum/Enum, same number of tags     ⟶  t                                                             632
ULift.{u}/ULift.{u}, u never 0     ⟶  up (cast A B e (down t))                                        [Q4, §4.1]
groundEqTy A B (equal, inert, ground) ⟶  t                     (regularity at inert types)   CONJECTURE (argued) [wiz, D1, P1]
Desc_l I / Desc_l I'               ⟶  by the description (below)                                  [wiz, D1]
μ^s D i / μ^s D i', t = con x      ⟶  con (cast (⟦D⟧ μ^s' i) (⟦D⟧ μ^s' i') ê x)                  [std: PT22, D1]
(a numeral at its own type: the line above, since the numeral type is ground)
ν^s D i / ν^s D i', t = cocon x    ⟶  cocon (cast (⟦D⟧ ν^s' i) (⟦D⟧ ν^s' i') ê x)                [wiz, D1]
otherwise                          ⟶  stuck
```

and `out (cast (ν^s D i) (ν^s D i') e t) ⟶ cast (⟦D⟧ ν^s' i) (⟦D⟧ ν^s' i') ê (out t)`
(an unfolding is cast as it is observed). Here `μ^s D i / μ^s D i'` means two `μ` types
of **one family**: equal levels, and index type, description and size syntactically
equal (`sameFamily?`); `s = ↑s'` or `s = s' = ∞`; and

```
ê := transp I i (λ j _. ⟦D⟧ X i ≡ ⟦D⟧ X j) (reflTy (⟦D⟧ X i)) i' e  :  ⟦D⟧ X i ≡ ⟦D⟧ X i'
```

with `X = λ j. μ^s' D j`. Descriptions are cast along `e : I ≡ I'` (`Desc_l I ≡ Desc_l I'`
computes to `I ≡ I'`):

```
cast (ret i)       ⟶  ret (cast I I' e i)
cast (arg q S E)   ⟶  arg q S (λ s. cast (Desc I) (Desc I') e (E s))
cast (rec q j E)   ⟶  rec q (cast I I' e j) (cast … e E)
cast (hrec q H j E) ⟶ hrec q H (λ h. cast I I' e (j h)) (cast … e E)
```

**No regularity** (D1, decision (a)). Until D1, the last line was "`t` if the two types
quote equal, whatever `e` is". With an impredicative `Prop` and definitionally irrelevant
equality that is exactly Abel and Coquand's setting [AC20], and a closed 18-line program
made both kernels loop (Status.md, D1). Regularity is now off in both kernels
(`Globals.regularity := .off`; `kernelRegularity` in `Kernel.wiz`); `wiz check
--regularity full` restores it for experiments. In its place, `cast` computes on data:

* **Why the μ rule is sound (subject reduction).** `e : μ D i ≡ μ D i'` computes to
  `i =_I i'`, so `ê` is a well-typed proof of the payload equation: `transp`'s motive
  `λ j _. ⟦D⟧ X i ≡ ⟦D⟧ X j` at `i` is `⟦D⟧ X i ≡ ⟦D⟧ X i`, proved by `reflTy`, and at `i'`
  is the goal. `x : ⟦D⟧ X i` (rule *con*, `X` at the predecessor size), so the inner cast
  has type `⟦D⟧ X i'` and `con` of it has type `μ^s D i'`. The rule uses nothing but
  `e`. The type equation is the code equation of PT22/CIC-obs for an inductive family
  with the parameters fixed: `μ D i ≡ μ D i'` iff `i = i'`. It is injective in the index,
  which holds in the setoid/inductive-recursive model where `μ D i` is a code. The
  equation computes only when `I`, `D`, the level and the size agree syntactically;
  otherwise it stays stuck, and the stuck form quotes back to the equation itself. So the
  rule's *result* is stable under substitution: syntactic equality is preserved by
  substitution. Syntactic *inequality* is not. Two stuck casts at convertible but
  syntactically different families can stop being convertible after a substitution
  makes only one of them fire. That is incompleteness, not unsoundness (Status.md, D1;
  the same holds for regularity at inert types, below).
  Families with different parameters (`List A ≡ List B`) stay stuck: their equation would
  need equality of descriptions, which is future work.
* **Why it blocks the D1 loop.** The rule casts *every* field, along the components of
  `ê`. A `Prop` field is cast between propositions, which applies the equivalence (`ê`'s
  component `.1`), a stuck proof. Abel–Coquand's box therefore yields `(… ).1 δ`, not `δ`,
  and `Ω` has a normal form. A field at a neutral type (`cast A A e a` for a variable `A`)
  is stuck, as in TTobs.
* **Regularity at inert types (CONJECTURE).** `inertTy` (`Eval.lean`; `inertTy` in
  `Kernel.wiz`) is a syntactic, conservative test: `Enum`, `Unit_l` with `l` never 0,
  `Σ` with a never-zero sort annotation of inert types, and `μ` types whose index type
  is inert and whose description, walked with its tags (and with a fresh variable for a
  non-enum field), has only `ret`, `rec` and `arg` at inert types (no `hrec`, no `Prop`
  field, no function, no neutral type, so no variable parameter: `List A` is not inert,
  `List Nat` is). At an inert `A`, `cast A A e t ⟶ t`. The argument that normalisation
  is preserved:
  - on a **neutral** `t`, the rule rewrites one neutral (`cast A A e t`) to another
    (`t`); neither is a redex for any eliminator of an inert type (`ind`, `ecase`,
    projections, `vNatView`), so no reduction is enabled that was blocked before;
  - on a **canonical** `t`, the structural rule computes a value equal to `t` except for
    the index proofs at its `ret` leaves (which become `ê`-components applied to them):
    convertible to `t` by proof irrelevance, and since an inert value contains no λ (its
    proofs are proofs of equations at inert index types, which compute to `True`, `False`
    and Σs of them, with no Π), no later reduction can tell the two apart;
  - after a substitution, a neutral `t` may become canonical; by the two cases the result
    is the same up to proof irrelevance, so reduction stays confluent up to conversion.
  Abel–Coquand's loop needs a cast that returns a *proof* (or a λ) unchanged; inert types
  hold neither. Conversion stays decidable as before: the new rules are evaluation rules
  that terminate (the inertness walk is bounded by the nesting depth 8 and by the finite
  enumerations; the payload cast follows the finite constructor value), and conversion
  is unchanged (proof irrelevance, η, structural comparison; `unCast` applies only under
  `--regularity full|nonprop|refl`). It is a conjecture: there is no normalisation proof
  for TTobs with this rule, though the argument above suggests it is admissible.

  **A more careful argument** (`/workspace/wiz-notes/inert-regularity.md`) corrects the
  one above in three places:
  1. The first bullet is too strong. Removing a stuck cast can make two types syntactically
     equal, and that *does* enable rules with syntactic side conditions (`sameFamily?`,
     the μ case of `vEqType`). Those are rules of the system without regularity, so
     termination is not at risk, but "no new redex" does not prove it.
  2. Inert values do contain proofs (the index equations). Convertible proofs can *reduce*
     differently, and the evaluator reduces proofs, so "no reduction can tell them apart"
     is not the reason. The reason is that inert types are **rigid**: their reducibility
     candidate does not depend on the interpretation of `Prop` or of type variables. At
     such a type, a rule that returns its argument unchanged keeps Girard's candidates
     argument valid, provided environments must agree at inert types, and that
     restriction is not circular because inert types mention no `Prop`. Abel–Coquand's
     construction needs a non-rigid type: one whose candidate is an impredicative
     intersection (`⊤ → ⊤`), or depends on a `Prop` variable (the box).
  3. The side condition was syntactic (`sameVal`), so algorithmic conversion was not a
     congruence for the rule (now fixed by ground equality, below: P1). For example, `cast (Fin (f p)) (Fin (f q)) e k` stays stuck
     for a variable `k`, although `Fin (f p) ≡ Fin (f q)` by irrelevance and the reflexive
     cast reduces to `k`. So conversion is not stable under substitution (Status.md, D1).
     That is incompleteness, not unsoundness. The fix is to decide the side condition with
     conversion.

  The note sketches three arguments:
  * consistency: the rule holds wherever `μ` is an initial algebra and `Prop` is
    proof-irrelevant;
  * normalisation of relevant terms: one trivial new case in a Pujet–Tabareau-style
    logical relation;
  * normalisation of proofs, which the evaluator needs because it reduces them: the
    candidates argument above.

  All three are **relative to the same property of the system without regularity**, which
  is itself unproved for Wiz. No counterexample was found. The note lists what one would
  need.
* **Cost.** Casting a constructor of a non-inert type walks the whole value (each field
  is cast). At inert types the cast is the identity.
* **The side condition is ground equality** (P1, `groundEqTy` in both kernels;
  `/workspace/wiz-notes/p1-stable.md`). A side condition must give the same answer for
  convertible inputs (S1), and an answer of "fires" must survive substitution (S2).
  Otherwise one side of a conversion reduces and the other is stuck, and a δβ-reduct of
  a well-typed term can be rejected. Syntactic equality fails S1 (proof arguments inside
  an index, `Fin (f p)` against `Fin (f q)`; a glued name against its unfolding).
  `groundEqTy A B` holds for two inert types that are equal and have no free variable in
  a relevant position:
  * types and descriptions are compared part by part (an `arg` at a non-tag field is
    compared under an atom, a variable bound by the comparison);
  * values are compared by their inert type: tags, numerals and constructors; `Unit` and
    propositions skipped; `Σ` by projections;
  * a neutral equals only the same atom.
  At an inert type, convertible values have the same canonical skeleton and neutrals in
  the same places, so S1 holds. A ground type has nothing to substitute, so S2 holds.
  What is lost: regularity at inert types whose indices are open (`cast (Fin n) (Fin n) e
  k` for variables `n`, `k` is stuck). Casts of constructors still compute structurally.
  `--inert conv` (experimental, Lean kernel) also identifies `cast A B e t` with `t` in
  conversion when `A` is inert and `A ≡ B` (InReg_conv, decided by `convTy`, so it is a
  congruence). `--inert syntactic` restores the old rule for comparison.
* **Syntactic equality** (`sameVal`, both kernels; now used only by the D1 experiment's
  `--regularity` modes) quotes at `max (lvlBound A)
  (lvlBound B)`, a level above every variable either value mentions, so different
  variables never quote alike (before `b7e1736` it was a fixed 100000: Status.md, Q3).

### 8.4a Propositional regularity: the `castRefl` axiom

The Prelude declares

```
axiom castRefl.{u} {0 A : Type u} (0 e : A = A) (0 a : A) : (cast e a : A) = a
```

It is an **axiom**: a proof, so it is a stuck neutral and never computes (`#reduce`
leaves `castRefl e a` alone), and `#print axioms` lists it for any declaration that uses it.
It is the propositional form of regularity that §8.4 removed from conversion. Proofs use it to
get rid of a stuck cast at a type variable: `Vec.map f (cons x xs)` is
`cons (cast B B _ (f x)) …`, and `Vec.map_cons` (`lib/Vec.wiz`) proves it equal to
`cons (f x) (Vec.map f xs)` by one `castRefl` at `Vec B (n+1)`. The cast in its type
computes to the same stuck casts as the definition, up to the proofs inside them, which
conversion ignores.

* **Consistency** [std: setoid model]. In the setoid/observational model, `cast A A e` is
  the identity up to the setoid equality of `A`, for any proof `e : A ≡ A`. So `castRefl`
  holds there, and it is consistent with the rest of the theory. A propositional equation
  can't break normalisation: it is a proof, irrelevant, and never reduces. The
  Abel–Coquand loop needs the *definitional* rule.
* **Canonicity.** As with any axiom, closed proofs mentioning it are not canonical, which
  is harmless because proofs are irrelevant and erased.

### 8.5 Proof irrelevance

At a type that is a proposition, any two elements are convertible (§11.2):

```
     Γ ⊢ A ⇒ Sort 0      (as computed by typeSort?, Conv.lean:213)
     ──────────────────────────────────────── conv-irr      [std: PT22; Gilbert et al. (unverified)]   Conv.lean:263
     Γ ⊢ a ≡ b : A
```

There are **no inductive propositions** (`μ` always lives in `Sort (l+1)`, §9), so there
is no large elimination out of `Prop` except through `absurd` (from `False`) and `split`
on a Σ of propositions (whose components are propositions too: subsingleton elimination).

---

## 9. Descriptions, μ and induction

Stage 4d. Inductive types are least fixed points of **descriptions**, first-class data,
in the style of levitation [CDMM10] (Wiz's `Desc` is a primitive, not levitated: `Desc`
itself is not `μ` of a description).

### 9.1 Descriptions

```
     Γ ⊢ I type@k    ⊢ k ≡ l+1
     ───────────────────────────────────── desc                                     Check.lean:511–514
     Γ ⊢ Desc.{l} I ⇒ Sort (l+2) ⊣ 0

     Γ ⊢ i ⇐ I ⊣ U
     ───────────────────────────────── ret                                           Check.lean:283
     Γ ⊢ ret i ⇐ Desc.{l} I ⊣ U

     Γ ⊢ q qty   Γ ⊢ S type@k   ⊢ k ≡ l+1   Γ ⊢ D ⇐ (ω s : S) → Desc.{l} I ⊣ U
     ───────────────────────────────── arg                                           Check.lean:284–289
     Γ ⊢ arg q S D ⇐ Desc.{l} I ⊣ U

     Γ ⊢ q qty   Γ ⊢ j ⇐ I ⊣ U₁   Γ ⊢ D ⇐ Desc.{l} I ⊣ U₂
     ───────────────────────────────── rec                                           Check.lean:290–294
     Γ ⊢ rec q j D ⇐ Desc.{l} I ⊣ U₁ + U₂

     Γ ⊢ q qty   Γ ⊢ H type@k   ⊢ k ≡ l+1   Γ ⊢ j ⇐ (ω h : H) → I ⊣ U₁   Γ ⊢ D ⇐ Desc.{l} I ⊣ U₂
     ───────────────────────────────── hrec                                          Check.lean:295–302
     Γ ⊢ hrec q H j D ⇐ Desc.{l} I ⊣ U₁ + U₂
```

(`ω` stands for the rig's `explicitDefault`.) `rec` is a recursive field at index `j`;
`hrec` is an infinitely branching recursive field `(h : H) → μ D (j h)`. Strict positivity
holds by construction: there is no way to mention the type being defined except through
`rec`/`hrec`. Fields carry quantities [wiz]; `ret`, `arg`, `rec` are levitation's
constructors [std: CDMM10]; `hrec` is the usual infinitary extension (unverified which
paper; Dagand's thesis has `Π`-fields).

**Field levels (Q4, fixed).** A field type (and the domain `H` of an infinitary field) must
be in **exactly** `Sort (l+1)`. The eliminator's method types (`delimMethodTys`) quantify
over `S : Sort (l+1)` and `H : Sort (l+1)`, and universes are not cumulative. Until Q4 the
rule was `k ≤ l+1`, and `Desc.elim` on a description with a smaller field passed `S :
Sort k` where `Sort (l+1)` was expected, so the reduct was not well typed (`getS D : Type`
reduced to `True : Prop`). With `k ≡ l+1`:

* **Subject reduction for `Desc.elim`.** `arg q S E ⇐ Desc.{l} I` gives `S : Sort (l+1)`
  and `E ⇐ (ω s : S) → Desc.{l} I`. The reduct `marg q S E (λ s. Desc.elim P m… (E s))` is
  then well typed against `marg`'s type: `q : Qty`, `S : Sort (l+1)` (now exactly the
  binder's sort), `E : S → Desc I`, and the hypothesis has type `(s : S) → P (E s)`, by the
  rule for `Desc.elim` at `E s : Desc I`; the result `P (arg q S E)` is the redex's type.
  `hrec` is the same with `H`. `ret` and `rec` were already fine. The templates of §9.2
  are closed terms typed by these rules, so `⟦D⟧`, `All`, `hyps` and `map` are well typed
  on every description; `ind`, `scase`, `sfix` and `coit`, whose reducts are built from
  them, inherit subject reduction (as far as it held before; their own arguments are
  unchanged).
* **Small fields are lifted by the elaborator** (§4.1, `Elab/Inductive.lean`: `ctorDesc`,
  `fieldLevels`, `FieldLift`). A field `x : S` with `S : Sort k`, `k ≢ l+1`, becomes
  `arg q (ULift.{l+1} S) (λ x. D[down x / x])`, the domain of an infinitary field
  `hrec q (ULift.{l+1} H) (λ h. js[down h / h]) D`, and the tag of a type above `Type`
  (`Enum ls : Type`, when `l+1 ≢ 1`) `arg ω (ULift.{l+1} (Enum ls)) (λ t. ecase (down t) …)`.
  So a proof field of a datatype in `Type` is lifted, and so is every field `A : Type u`
  of a type in `Type (max u v)` (`Prod.{u,v}`), and the tag of every level-polymorphic
  inductive type. Constructors take the field itself and put `up x` (or `fun h => f
  (down h)`) in the payload; recursors (`casesOn`, `rec`), and so patterns and structural
  recursion, receive `down` of it (or `fun h => f (up h)`), with the induction hypotheses
  of a lifted infinitary field read the same way. The printer hides `up` and `down`.
  The surface `Desc.arg` already required `S : Sort (l+1)` exactly.
* `Kernel.wiz` has the same rule (`lvlEquiv`), and the same `ULift` (§15). Its frontend
  (`Frontend.wiz`) builds descriptions at `Desc.{0}` from a surface language without
  `Prop`, equations or universe polymorphism, so every field it can build is in `Type`
  and needs no lifting.

The eliminator:

```
     Γ ⊢ D ⇒ T ⊣ U_D    whnf T = Desc.{l} I
     Γ ⊢ P ⇐ (ω _ : Desc.{l} I) → Sort v
     Γ ⊢ mret ⇐ (i : I) → P (ret i)                                       ⊣ U₁
     Γ ⊢ marg ⇐ (q : Qty) → (S : Sort (l+1)) → (E : S → Desc I) → (ih : (s : S) → P (E s)) → P (arg q S E)   ⊣ U₂
     Γ ⊢ mrec ⇐ (q : Qty) → (j : I) → (E : Desc I) → (ih : P E) → P (rec q j E)                               ⊣ U₃
     Γ ⊢ mhrec ⇐ (q : Qty) → (H : Sort (l+1)) → (j : H → I) → (E : Desc I) → (ih : P E) → P (hrec q H j E)   ⊣ U₄
     ─────────────────────────────────────────────── Desc.elim     [wiz]        Check.lean:515–526
     Γ ⊢ Desc.elim.{v} P mret marg mrec mhrec D ⇒ P D ⊣ ω·(U₁+U₂+U₃+U₄) + U_D

     Desc.elim P m… (ret i)       ⟶ mret i                                                   vDelim, Eval.lean:355–371
     Desc.elim P m… (arg q S E)   ⟶ marg q S E (λs. Desc.elim P m… (E s))
     Desc.elim P m… (rec q j E)   ⟶ mrec q j E (Desc.elim P m… E)
     Desc.elim P m… (hrec q H j E) ⟶ mhrec q H j E (Desc.elim P m… E)
```

All binders in these method types have quantity `ω` (`explicitDefault`).

### 9.2 Interpretation, All, hyps, map (templates)

`⟦D⟧ X i`, `All D X P i xs`, `hyps` and `map` are **not kernel rules**. They are closed
terms built with `Desc.elim` (`Templates.lean`), evaluated like any term:

```
⟦ret j⟧ X i        = (0 _ : j =_I i) × Unit_{l+1}
⟦arg q S D⟧ X i    = (q s : S) × ⟦D s⟧ X i
⟦rec q j D⟧ X i    = (q _ : X j) × ⟦D⟧ X i
⟦hrec q H j D⟧ X i = (q _ : (h : H) → X (j h)) × ⟦D⟧ X i
All (ret j) …            = Unit
All (arg …) P i xs       = All (D xs.1) P i xs.2
All (rec …) P i xs       = P j xs.1 × All D P i xs.2
All (hrec …) P i xs      = ((h : H) → P (j h) (xs.1 h)) × All D P i xs.2
```

Indices are handled by an **equation** `j = i` in the payload (the "Henry Ford"
encoding), so `μ` needs no index unification. The templates are **trusted**: the kernel
never type-checks them, and their Σ types carry hand-written sort annotations
(`Templates.lean:44–75`). An error there would be a kernel bug (Status.md, kernel trust).

### 9.3 μ, con, ind

```
     Γ ⊢ I type@k   ⊢ k ≡ l+1   Γ ⊢ D ⇐ Desc.{l} I   Γ ⊢ i ⇐ I
     ───────────────────────────────────── mu       (the size s is NOT checked; see below)   Check.lean:527–533
     Γ ⊢ μ.{l} I D i ^s ⇒ Sort (l+1) ⊣ 0

     s = ↑s'  or  s = ∞ (then s' = ∞)      Γ ⊢ x ⇐ ⟦D⟧ (λj. μ^{s'} D j) i ⊣ U
     ───────────────────────────────────── con   (check only)                              Check.lean:303–306
     Γ ⊢ con x ⇐ μ.{l} I D i ^s ⊣ U

     Γ ⊢ I type@_   Γ ⊢ D ⇐ Desc.{l} I
     Γ ⊢ P ⇐ (ω i : I) → (ω _ : μ D i ^∞) → Sort v
     Γ ⊢ m ⇐ (0 i : I) → (ω xs : ⟦D⟧ (μ D) i) → (ω ih : All D (μ D) P i xs) → P i (con xs)   ⊣ U_m
     Γ ⊢ i ⇐ I    Γ ⊢ x ⇐ μ D i ^∞ ⊣ U_x
     ───────────────────────────────────── ind                                               Check.lean:534–546
     Γ ⊢ ind P m i x ⇒ P i x ⊣ ω·U_m + U_x

     ind P m i (con xs)  ⟶  m i xs (hyps D (μ D) P (λj y. ind P m j y) i xs)                vIndStep, Eval.lean:409–423
```

* `μ` is always in `Sort (l+1)`: there are no inductive propositions.
* The size argument of `μ` (and `ν`) is checked erased: `Γ⁰ ⊢ s ⇐ Size` (since
  `4605514`; Status.md, K3).
* The method's usage is scaled by ω (`QRig.many?`) because the method may run once per
  node (§5.3; Status.md, Q2).
* `x` is checked against `μ^∞`; a value of a smaller size is accepted by subtyping.

### 9.4 Numerals [impl]

After `builtin nat := N` (and `nat.zero`, `nat.succ`, `nat.add`, …), a numeral `n`
infers `N` (`Check.lean:341–343`), and evaluation treats it as `succⁿ zero`, unfolding one
step whenever something looks inside (`vNatView`, `Eval.lean:376`). The registered
operations compute natively on two literals and otherwise use their definitions
(`vNatOp`, `Eval.lean:386`). `a =_N b` on two literals is decided directly
(`Eval.lean:516`). `ind` on a numeral is glued (`Val.lazyInd`) so that it computes lazily.
**Nothing checks that a registration is correct** (that `N` is a natural-number type and
that the native operation agrees with the registered definition). The registrations are
trusted like axioms (§13, Status.md, O3).

---

## 10. Sizes, ν and sized (co)recursion

Stage 4f. Sizes follow Abel's sized types [AVW17 and earlier work], with Wiz's own
choices marked.

### 10.1 Sizes

```
  ──────────────────── Size      ────────────── ∞      Γ⁰ ⊢ s ⇐ Size            Γ⁰ ⊢ s ⇐ Size
  Γ ⊢ Size ⇒ Sort 1 ⊣ 0          Γ ⊢ ∞ ⇒ Size ⊣ 0     ──────────────── ↑       ──────────────────── Size<
                                                       Γ ⊢ ↑s ⇒ Size ⊣ 0         Γ ⊢ Size< s ⇒ Sort 1 ⊣ 0
                                                                                 Check.lean:487–490

     Γ⁰ ⊢ t ⇐ Size      Γ ⊢ t < s
     ──────────────────────────────── size-lt (check only)        Check.lean:277–282
     Γ ⊢ t ⇐ Size< s ⊣ 0
```

Evaluation identifies `↑∞` with `∞` (`Eval.lean:182–184`). A size is viewed as `↑ᵏ ∞` or
`↑ᵏ x` for a variable `x` (`sizeView`, `Conv.lean:105`). The order (`Conv.lean:126–150`):

```
s ≤ ∞                       for every s
↑ᵏ x ≤ ↑ᵐ x                 when k ≤ m
↑ᵏ x ≤ b                    when x : Size< u in Γ and ↑ᵏ⁻¹ u ≤ b   (k ≥ 1),  or u ≤ b (k = 0)
∞ ≤ ↑ᵐ x                    never

a < b   (b not ∞)           ⇔ ↑a ≤ b
a < ∞                       ⇔ a = ↑ᵏ x for a variable x : Size< u        (DECISION D2)
```

* **D2 [wiz]: `∞` is not below itself.** Because `↑∞ = ∞`, the rule `a < b ⇔ ↑a ≤ b`
  would give `∞ < ∞`. Agda's `∞ < ∞` makes well-founded induction on sizes inconsistent
  (Agda issue #3026). Wiz admits below `∞` only `↑ᵏ x` for a *bounded* variable `x`; a
  variable of type `Size` is not below `∞` (it may stand for `∞`). Fixed in `fb9074d`
  (Status.md, F2).
* Size equality in conversion is **syntactic on the view** (`sizeEq`, `Conv.lean:117`):
  same base variable and same number of `↑`s, or both `∞`.

### 10.2 Sized μ: sfix, scase

```
     (I, D, P as for ind)
     Γ ⊢ f ⇐ (0 s : Size) → (ω rec : (0 j : Size< s) → (ω i : I) → (ω y : μ^j D i) → P i y)
                         → (ω i : I) → (ω x : μ^s D i) → P i x                        ⊣ U_f
     Γ⁰ ⊢ s ⇐ Size    Γ ⊢ i ⇐ I    Γ ⊢ x ⇐ μ^s D i ⊣ U_x
     ───────────────────────────────────── sfix                     Check.lean:553–565, sfixFunTy Conv.lean:162
     Γ ⊢ sfix P f s i x ⇒ P i x ⊣ ω·U_f + U_x

     sfix P f s i (con xs)  ⟶  f ∞ (λj i y. sfix P f j i y) i (con xs)                     vSfix, Eval.lean:436–449

     Γ⁰ ⊢ s ⇐ Size
     Γ ⊢ m ⇐ (0 j : Size< s) → (0 i : I) → (ω xs : ⟦D⟧ (λj'. μ^j D j') i) → P i (con xs)   ⊣ U_m
     Γ ⊢ i ⇐ I    Γ ⊢ x ⇐ μ^s D i ⊣ U_x
     ───────────────────────────────────── scase                    Check.lean:579–592, scaseMethodTy Conv.lean:172
     Γ ⊢ scase P m s i x ⇒ P i x ⊣ U_m + U_x

     scase P m s i (con xs)  ⟶  m ∞ i xs                                                   vScase, Eval.lean:453–462
```

* `sfix` unfolds **only on a constructor** (as in MiniAgda / AVW17), so its unfolding can't
  loop on a neutral argument. Its recursive calls are typed at sizes below the generic
  `s`; at run time they are taken at `∞`, since sizes are irrelevant. In the unfolding,
  `f ∞` expects `rec : (j : Size< ∞) → …`; the reduct is typed by subtyping
  (`μ^s ≤ μ^∞`).
* `scase`'s method runs once, so it is not scaled.

### 10.3 ν, out, cocon, coit, scofix

```
     (same premises as mu)
     ───────────────────────────────────── nu   (size not checked)                          Check.lean:527–533
     Γ ⊢ ν.{l} I D i ^s ⇒ Sort (l+1) ⊣ 0

     Γ ⊢ x ⇒ T ⊣ U    whnf T = ν D i ^s    s = ↑s' or s = ∞ (s' = ∞)
     ───────────────────────────────────── out                                               Check.lean:547–552
     Γ ⊢ out x ⇒ ⟦D⟧ (λj. ν^{s'} D j) i ⊣ U

     s = ↑s' or s = ∞ (s' = ∞)      Γ ⊢ x ⇐ ⟦D⟧ (λj. ν^{s'} D j) i ⊣ U
     ───────────────────────────────────── cocon (check only)                                Check.lean:307–310
     Γ ⊢ cocon x ⇐ ν D i ^s ⊣ U

     Γ ⊢ S ⇐ (ω i : I) → Sort (l+1)
     Γ ⊢ step ⇐ (ω i : I) → (ω s : S i) → ⟦D⟧ S i ⊣ U_st     Γ ⊢ i ⇐ I    Γ ⊢ t ⇐ S i ⊣ U_t
     ───────────────────────────────────── coit                                              Check.lean:594–606
     Γ ⊢ coit S step i t ⇒ ν D i ^∞ ⊣ ω·U_st + U_t

     Γ ⊢ A ⇐ (ω i : I) → Sort (l+1)
     Γ ⊢ f ⇐ (0 s : Size) → (ω rec : (ω i : I) → A i → ν^s D i) → (ω i : I) → A i → ν^{↑s} D i   ⊣ U_f
     Γ⁰ ⊢ s ⇐ Size    Γ ⊢ i ⇐ I    Γ ⊢ a ⇐ A i ⊣ U_a
     ───────────────────────────────────── scofix                     Check.lean:566–578, scofixFunTy Conv.lean:180
     Γ ⊢ scofix A f s i a ⇒ ν D i ^s ⊣ ω·U_f + U_a

     out (cocon xs)               ⟶  xs                                                     vOut, Eval.lean:468–487
     out (coit S step i t)        ⟶  map D S (ν D) (λj s. coit S step j s) i (step i t)
     out (scofix A f s i a)       ⟶  out (f ∞ (λi a. scofix A f ∞ i a) i a)
```

* `coit`, `scofix` are **values** (`Val.coit`, `Val.scofix`): they unfold only under `out`
  (the guard against infinite unfolding). [std: Abel's sized coinduction; the
  "unfold under observation" strategy is standard (unverified which paper exactly)]
* `ν` is contravariant in its size (§11.5): `ν^∞ ≤ ν^s`.
* `out` requires the size to be visibly a successor or `∞`. Inside `f`, `rec` returns
  `ν^s` for the generic `s`, which can't be observed; this is the productivity check.

---

## 11. Definitional equality and subtyping

The conversion algorithm is **type-directed** (`conv ty a b`), on values in whnf.
There is no separate declarative definitional equality: the algorithm *is* the
specification. The rules below describe what it equates. [std: Abel & Coquand 2007's
type-directed algorithmic equality, cited in `Conv.lean:24`; not re-checked]

### 11.1 Unfolding (δ, ζ, β, ι)

* **β**: `(λx. b) a ⟶ b[a/x]` (`vApp`, `Eval.lean:269`); `(a, b).1 ⟶ a`,
  `(a, b).2 ⟶ b`, `let (x, y) := (a, b); u ⟶ u[a, b]` (`vSplit`, `Eval.lean:295`).
* **ζ**: `let x := v; b ⟶ b[v/x]` (`Eval.lean:142`).
* **δ**: a global with a definition unfolds to it, instantiated at the given levels
  (`Eval.lean:131–135`). It is **glued** [impl]: the value keeps the name and its spine
  and unfolds lazily, so `f a ≡ f b` is first tried by comparing the spines
  (`convGlued`, `Conv.lean:358`); if that fails, both sides are unfolded. Axioms (no
  definition) and partial definitions are neutral heads.
* **ι**: the eliminator rules of §7–§10 and the equality computations of §8.

### 11.2 conv at a type

`conv` (`Conv.lean:252–313`), after unfolding glued values and comparing two numerals
directly:

```
1. proof irrelevance    if typeSort?(A) ≡ 0:   a ≡ b                                   263   [std: PT22]
2. regularity           (only under --regularity full|nonprop|refl; off by default)       264–265, 307–310  [wiz]
                        replace a stuck cast A' B' e t (empty spine) with A' ≡ B' by t,
                        on both sides, before comparing
3. by the type:
   Π   η:  a x ≡ b x  at B x, for a fresh x : A                                         267–269  [std]
   Σ   η:  a.1 ≡ b.1 : A  and  a.2 ≡ b.2 : B a.1                                        270–272  [std]
   Unit_l:  always                                                                       273      [std: η for unit]
   ULift A:  η:  down a ≡ down b : A                                                       [std; Q4]
   Qty:   as polynomials (equivalent under all assignments), else neutral comparison    274–276  [wiz]
   Enum:  same tag index, else neutral comparison                                        277–279
   Size, Size< s:  sizeEq                                                                280      [wiz]
   Desc:  structurally (ret/arg/rec/hrec), else neutral comparison                       281–291
   μ:     con x ≡ con y  if x ≡ y at the payload type; else neutral comparison           292–294
   ν:     cocon/cocon, scofix/scofix, coit/coit componentwise; else neutral comparison   295–303  [wiz]
   Sort:  convTy                                                                         304
   otherwise: neutral comparison (convNe)                                                305
```

`typeSort?` (`Conv.lean:213–229`) computes a type's universe from its value (Π: `imax`
of the parts; neutral: from `inferNe`), independently of the sort annotations. So proof
irrelevance does not depend on the annotations.

At `ν`, two coinductive values are equal only if they are built the same way. This is
sound (it equates less than bisimilarity) and incomplete.

### 11.3 convTy

`convTy` (`Conv.lean:326–354`) compares types structurally:

```
Sort u ≡ Sort u'                 ⊢ u ≡ u'
Π/Π, Σ/Σ                         same quantity (or the Π/Σ is a proposition: quantities don't matter),
                                 domains ≡, codomains ≡ under a fresh variable
Qty ≡ Qty, Size ≡ Size           always
Size< s ≡ Size< t                sizeEq s t
Enum ls ≡ Enum ls'               |ls| = |ls'|
Desc l I ≡ Desc l' I'            l ≡ l', I ≡ I'
μ/μ, ν/ν                         l ≡ l', sizeEq, I ≡ I', D ≡ D' : Desc, i ≡ i' : I
Unit_u ≡ Unit_u', Empty_u ≡ Empty_u'   u ≡ u'
ULift.{u} A ≡ ULift.{u'} A'      u ≡ u', A ≡ A'
two neutrals                     convNe
```

The sort annotations are ignored by conversion.

### 11.4 convNe

Two neutrals are equal when their heads are equal and their spines are pointwise
convertible at the types computed along the spine (`Conv.lean:388–467`). Heads:
the same variable; the same global at equivalent levels; two stuck equations with
convertible parts; two stuck casts with convertible types and arguments (the proofs `e`
are **not** compared); and **any two proof heads** (`refl`, `reflTy`, `transp`) are equal
(proof irrelevance at the head). Eliminations compare their motives and methods at the
types the kernel would give them.

### 11.5 Subtyping

`subTy` (`Conv.lean:474–489`) is conversion plus sizes [std: AVW17 (sizes); wiz in detail]:

```
μ^s D i ≤ μ^t D' i'     if s ≤ t and the rest is convertible       (covariant)
ν^s D i ≤ ν^t D' i'     if t ≤ s and the rest is convertible       (contravariant)
Π: (q x : A₁) → B₁ ≤ (q' x : A₂) → B₂   if q ≡ q' (or the Π is a proposition), A₂ ≤ A₁, B₁ ≤ B₂
Σ: covariant in both parts, quantities equal
Size< s ≤ Size,   Size< s ≤ Size< t if s ≤ t
otherwise convTy
```

Subtyping is used only by the mode switch (§6) and is **not** reflected in
observational equality (`μ^s ≡ μ^t` as types is stuck, §8.3).

---

## 12. Evaluation strategy

`eval` (`Eval.lean:128`) is call-by-value on an environment, with closures for binders.
Lazy places: glued globals and `ind` on numerals (thunks); `coit`/`scofix` values (until
`out`); `ecase` branches (evaluated only when the tag is known). Ill-typed situations
(applying a non-function) `panic!` and are meant to be unreachable on checked terms. All
functions are `partial` in Lean: **termination of evaluation and of type checking is not
proved**, and the D1 experiment shows checking can loop (Status.md).

---

## 13. Global declarations and universe polymorphism

```
     name ∉ Σ    level parameters ν₁…νₖ distinct    every level parameter used is among them
     · ⊢ T type@_        (value v given ⇒  · ⊢ v ⇐ T)
     ────────────────────────────────────────── addDecl                Check.lean:669–681
     Σ ⊢ c.{ν₁…νₖ} : T [:= v]   added

     c.{ν…} : T ∈ Σ     |us| = k
     ────────────────────────────────────── const                       Check.lean:347–352
     Γ ⊢ c.{us} ⇒ T[us/ν] ⊣ 0
```

* Declarations are checked **once, at symbolic levels**; a use instantiates the
  parameters [std: Lean 4]. Constants have no local usage (`⊣ 0`): globals are not
  tracked by QTT.
* **No recursion in the kernel:** a declaration is checked against the environment
  *without* itself, so a value cannot mention its own name.
* **Axioms** (`value = none`) are accepted with any well-formed type, including `False`.
* **Partial definitions** (`addPartialImpl`, `Check.lean:687`): `f` is added as an
  **axiom**, and its recursive implementation is checked against `f`'s type but used only
  by the compiler. The kernel never unfolds it. That the type is inhabited (so that the
  axiom is harmless) is checked by the **elaborator** (`inhabitedTy`,
  `Elab/Command.lean:576`), not by the kernel (Status.md, O2: this check can be fooled, and a proof of `False` was built).
* **`builtin` registrations** (`Elab/Command.lean:937–944`) are not checked by the kernel
  at all (§9.4; Status.md, O3).
* `Decl.inline` (evaluate eagerly) and `Decl.impl` (compiler implementation) do not affect
  what the kernel accepts.

*Kernel.wiz.* There is no global table: a constant term carries its value and type
(`Tm.const`, `Kernel.wiz:118`), and the kernel trusts that this pair was checked
(`Kernel.wiz:2070`). `checkDecl` (`Kernel.wiz:2211`) checks a declaration at symbolic
levels. Data levels (`μ.{l}`, `Desc.{l}`) are closed numerals.

---

## 14. Where the code and the stage docs disagree

Each item says what the code does; the code is what the kernel checks.

1. **Regularity.** Stages 4c/4e ([stages/04-data.md](stages/04-data.md)) describe regularity (`cast A A e t ≡ t`) as it was before
   D1. Since D1 it is off by default in both kernels, except at inert types (§8.4); the
   sections say so.
2. **`absurd`'s usage.** The rule in `Check.lean`'s docstring (`Check.lean:78–80`) gives
   `absurd M t ⊣ U` (the scrutinee's usage). The code returns `⊣ 0` and checks `t` in
   erased mode (`Check.lean:427–433`).
3. **Method scaling.** Stage 4d ([stages/04-data.md](stages/04-data.md)) and the docstring (`Check.lean:116–121`) say methods are
   scaled by ω. The code scaled by the rig's `explicitDefault`, which is ω only for
   `ZeroOneMany`; for the `Nat` rig it is `1`, which under-counts a method that runs once
   per node. **Resolved** in `a986c02`: the code now scales by `QRig.many?` (Q2).
4. **Linear pairs.** Stage 4b ([stages/04-data.md](stages/04-data.md)): "a linear pair is consumed with `let 1 (x, y) := p`". The
   code also lets `p.2` (and `p.1` when the field allows it) consume a linear pair, dropping
   the other component (§7.1).
5. **Missing rules in the docstring.** `Check.lean`'s rules omit the sort annotation on
   Π/Σ, the `sizeLt` check, `sfix`, `scase`, `scofix`, `cocon`, and the `isNeverZero`
   premise of `refl`. Its `eq` rule writes `l ≠ 0`; the code requires `isNeverZero l`
   (nonzero under *every* instantiation), which is stronger.
6. **`Term.lean`'s module comment** (`Term.lean:27`) says "Not in the core yet: μ/ν data and
   Σ-types (stage 4)". Both are in the core.
7. **`Eval.lean`'s module comment** (`Eval.lean:20–22`) says globals are δ-unfolded
   eagerly. They are glued (unfolded lazily) unless marked `inline` or `eager`.
8. **The OTT table in stage 4c** ([stages/04-data.md](stages/04-data.md)) writes funext as `(x : A) → a x = b x`; the code uses
   quantity 0 for `x`. It writes `Type u` equality as "structural equality of types;
   `False` for different formers", but propositions inside types are compared by
   equivalence, and `μ`/`ν`/`Desc` are stuck. (The prose below the table says the first
   part.)
9. **Sort annotations.** Stage 4c ([stages/04-data.md](stages/04-data.md)) says a Π/Σ "carries its sort (the elaborator writes
   it)". On `solutions` at `9717950`, several Π/Σ the elaborator builds carry none
   (the stage docs themselves list them only on the unmerged `agent/elab-sorts` branch, commit
   `31395a2`). After that branch merges, the remaining unannotated cases are "a Π/Σ under
   a `fun` whose variable's type isn't written down, or one that still mentions a
   metavariable".
10. **Self-hosting stages 14g–14p** ([stages/14-selfhost-kernel.md](stages/14-selfhost-kernel.md)) describe `Kernel.wiz` as mirroring the Lean
    kernel. It differs in the places listed in §15, one of which is unsound.

---

## 15. The self-hosted kernel (`Kernel.wiz`)

`Kernel.wiz` implements the same algorithm for a fragment, and the differential test
(Status.md) compares the two on random and hand-picked terms. Differences:

| topic | Lean kernel | Kernel.wiz |
|---|---|---|
| quantities | any `QRig`, quantity variables, `Qty` | literals `0, 1, ω` only (`Q`, `Kernel.wiz:19`); no `Qty` type |
| description fields | carry a quantity | carry none; the methods receive `tt` (`Kernel.wiz:830–845`) |
| `split` (`let (x, y)`) | yes | **no** |
| numerals, `natOp` | yes | no |
| levels of data | `Level` | closed numerals (`descr l`, `mu l`, `ulift l`) |
| `ULift` (Q4) | `ulift`/`up`/`down`, `cast` needs a level never `0` | `ulift`/`up`/`down` at closed levels (`vulift`, `vup`, `sdown`); the same rules |
| globals | table, by name | inline `const` terms carrying value and type (trusted) |
| **`Size ≡ Size`, `Size< s ≡ Size< t`** | **stuck** (`Eval.lean:572`) | **`False`**: `canonical` includes `vsize`/`vsizeLt` (`Kernel.wiz:552–565`) and `vEqTypeW` has no case for two sizes, so it falls through to "different formers ⇒ False" (`Kernel.wiz:961–963`). **Unsound** (Status.md, O1). |
| regularity in conversion (`unCast`) | off by default (`Conv.lean:264`, only under `--regularity`) | no: stuck casts are compared structurally |
| regularity in evaluation | off; at inert types only (`inertTy`) | the same (`kernelRegularity := .false`; `inertTy`) |
| convTy at Π/Σ propositions | quantities may differ | quantities must be equal (`Kernel.wiz:1598`) |
| proof irrelevance at Π/Σ | asked at the Π/Σ | asked at the codomain/components only (`Kernel.wiz:1537–1541`); equivalent |
| `isProp` | `typeSort? ≡ 0` | Π: codomain is a proposition; Σ: both parts (`Kernel.wiz:1328`) |
| size equality on non-variable bases | equal if the same metavariable | never (`sizeEq`, `Kernel.wiz:1388`) |
| `app` | evaluates the argument | only if the codomain may mention it (`usesVar`) |
| conversion fast path | none | `valSame`: bounded structural equality (`Kernel.wiz:1461`) |
| μ/ν size argument | unchecked | unchecked (`Kernel.wiz:1918, 1967`) |

---

## 16. What is not in the core, and who checks what

**Elaborator-only features** (they produce core terms, which the kernel checks):

* metavariables, unification, implicit arguments, type classes and instance resolution,
  level metavariables and defaulting (unconstrained size metavariables default to `∞`);
* `inductive`/`structure`/`coinductive` (they elaborate to descriptions, `μ`/`ν` and
  constructors), Lean-style `T.rec`, `T.casesOn`, `T.scasesOn` (built on `ind`, `ecase`,
  `cast`, `scase`);
* `match`, equations, structural and sized recursion (compiled to `ind`, `sfix`,
  `scase`), copatterns (compiled to `coit`, `cocon`), coconstructors `T.mk`, the
  guardedness check;
* macros, command macros and reflection, tactics, `deriving`, `do` notation;
* writing sort annotations on Π/Σ (the kernel checks those that are present).

**What the kernel re-checks.** Every `def`, `axiom`, constructor, recursor and generated
declaration goes through `addDecl` (`Elab/Command.lean:700–705`), which type-checks it
from scratch; a bug in elaboration, `match` compilation or recursion compilation can only
make the kernel *reject* a declaration. The kernel does not look at binder info, display
hints, or names.

**What the kernel trusts** (each is a place where a bug, or a wrong user declaration,
is not caught by type checking):

1. **Axioms** (`axiom`, and `C.*` functions from imported C headers, `foreign` types).
   The Prelude has one, `castRefl` (§8.4a).
2. **Partial definitions**: the kernel trusts the elaborator's inhabitedness check
   (`inhabitedTy`).
3. **`builtin` registrations**: numerals' type and native arithmetic.
4. **The templates** (`Templates.lean`): never type-checked; their sort annotations are
   hand-written.
5. **The method/motive types** the kernel builds itself (`delimMethodTys`,
   `indMethodTy`, `sfixFunTy`, … in `Conv.lean`), and the terms built inside `vEq`,
   `vEqType`, `vCast` (their binders and `some 0` annotations).
6. **Code outside the kernel that runs on checked terms**: erasure and the backends.
   Erasure relies on QTT: a 0-quantity value is assumed unneeded.
7. **The Lean compiler and runtime** (for the Lean kernel), and Wiz's own backend (for
   `Kernel.wiz`).

---

## 17. References

Checked for this document (title, authors, venue):

* **[Atkey18]** R. Atkey. *Syntax and Semantics of Quantitative Type Theory.* LICS 2018,
  pp. 56–65. doi:10.1145/3209108.3209189. (QTT; dependent tensor with `let`
  elimination; fixes the substitution problem of McBride's system.)
* **[AC20]** A. Abel, T. Coquand. *Failure of Normalization in Impredicative Type Theory
  with Proof-Irrelevant Propositional Equality.* LMCS 16(2), 2020. arXiv:1911.08174.
* **[CDMM10]** J. Chapman, P.-É. Dagand, C. McBride, P. Morris. *The Gentle Art of
  Levitation.* ICFP 2010, pp. 3–14. doi:10.1145/1863543.1863547.
* **[AVW17]** A. Abel, A. Vezzosi, T. Winterhalter. *Normalization by Evaluation for Sized
  Dependent Types.* PACMPL 1 (ICFP), 2017. doi:10.1145/3110277.
* **[PT22]** L. Pujet, N. Tabareau. *Observational Equality: Now for Good.* PACMPL 6
  (POPL), 2022. doi:10.1145/3498693. (TTobs.) The details of its rules quoted above
  (orientation of the Π domain equation, whether it has definitional regularity) were
  **not** re-checked against the paper.
* **[PT23]** L. Pujet, N. Tabareau. *Impredicative Observational Equality.* PACMPL 7
  (POPL), 2023, pp. 2171–2196. (CCobs: TTobs with an impredicative universe of
  definitionally proof-irrelevant propositions; decidability of conversion.)
* **Agda issue #3026**, "Well-founded induction on Size is inconsistent"
  (github.com/agda/agda/issues/3026).

Cited from the code or from memory, **not re-checked**:

* **[McBride16]** C. McBride. *I Got Plenty o' Nuttin'.* In *A List of Successes That Can
  Change the World*, LNCS 9600, 2016.
* **[AMS07]** T. Altenkirch, C. McBride, W. Swierstra. *Observational Equality, Now!*
  PLPV 2007.
* **[ML84]** P. Martin-Löf. *Intuitionistic Type Theory.* Bibliopolis, 1984.
* A. Abel, T. Coquand. *Untyped Algorithmic Equality for Martin-Löf's Logical Framework
  with Surjective Pairs.* TLCA 2005 / Fundamenta Informaticae 2007 (cited in
  `Conv.lean`).
* G. Gilbert, J. Cockx, M. Sozeau, N. Tabareau. *Definitional Proof-Irrelevance without
  K.* POPL 2019.
* A. Kovács, *elaboration-zoo* (cited in `Value.lean` for the NbE design).
