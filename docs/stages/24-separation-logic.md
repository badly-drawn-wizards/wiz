# Stage 24: separation logic

A shallow separation logic as a library, following Charguéraud's *Separation Logic
Foundations* (Software Foundations vol. 6, "SLF") chapter for chapter: the logic of
propositions (24a), heap predicates over a model heap (24b), and Hoare triples with the
frame rule over a small heap language (24c). There is no kernel support and no new
quantity: everything is ordinary Wiz definitions and proofs, checked by the kernel, and
**no law needs an axiom**. Plan: `concurrency-seplogic-plan.md`, stages S0–S2;
decisions CS7 (shallow model-heap logic first, then linear points-to tokens over a native
heap via `implemented_by`), CS10 (first-order concurrent SL with PCM ghost state next).
Tests: `lake test -- seplogic`.

## 24a: propositional logic over `Prop` ✅

`lib/Logic.wiz` (`import Logic`). Wiz has no inductive propositions (`μ` always lives in
`Type`), so the connectives are built from what the kernel has:

| | definition | rules |
|---|---|---|
| `P ∧ Q` | `P × Q` (a Σ of propositions is a proposition) | `And.intro/left/right/elim/symm/imp` |
| `P ∨ Q` | `(0 R : Prop) → (P → R) → (Q → R) → R` | `Or.inl/inr/elim/symm/imp/resolveLeft/resolveRight` |
| `Ex P` (∃) | `(0 R : Prop) → ((a : A) → P a → R) → R` | `Ex.intro/elim/imp`, `Ex.notForall` |
| `P ↔ Q` | `(P → Q) × (Q → P)` | `Iff.intro/mp/mpr/refl/symm/trans`, `Iff.toEq`, `Iff.ofEq` |
| `Not P` | `P → False` | `Not.elim`, `absurdOf` |

∨ and ∃ are the impredicative Church encodings; their eliminators go into propositions
only, as Lean's do. Since observational equality computes, `propext` (`Iff.toEq`) and
`funext` are one-liners: an equation of propositions *is* a pair of implications and an
equation of functions *is* pointwise. `Eq.symm/trans/congrArg/substProp` are J in its usual
shapes (lib/Vec.wiz now imports Logic for them). The names are Lean's, so the library can
move to native inductive propositions (plan D4) without renaming.

Two things about quantities that every proof here runs into:

* An equation computes to a Π/Σ with **erased** binders: `f = g` is
  `(0 x : A) → f x = g x`, `P = Q` is `(0 _ : (0 _ : P) → Q) × ((0 _ : Q) → P)`. A lambda
  checked against such a binder may not use its variable relevantly, and the first field
  of such a Σ can't be projected outside erased code. So `funext` and `Heap.ext`/`HProp.ext`
  take the *unerased* form and let subtyping convert it (quantities don't matter in a Π
  that is a proposition, CoreSpec §11.5), and `Iff.ofEq` gets the first direction from
  `Eq.symm`.
* Proofs are checked with usage like programs. Predicates are bound at 0 (they only occur
  in types), data at ω (pointwise lemmas match on it), and `transp` motives avoid using
  their variable (so `Eq.substProp` goes through `congrArg`; the Prelude's `Eq.subst` is the linear transport into a `Type`). Wishful:
  `erased-use-in-types`.

## 24b: heaps and heap predicates ✅

`lib/HProp.wiz` (`import HProp`), SLF chapters Hprop and Himpl.

* **Heaps** are total functions `Heap V := Nat → Option V` (SLF uses finite maps; the
  logic doesn't need finiteness, and 24c gets fresh locations from a bound). `Heap.union`
  is pointwise left-biased choice, `Heap.Disj h₁ h₂` says every location is free in one of
  them. Union laws (unit, associativity, commutativity under disjointness) and
  disjointness laws are proved pointwise on `Option`.
* **Heap predicates** `HProp V := Heap V → Prop` with `emp`, `l ↦ v`, `hpure P` (SLF's
  `\[P]`), `htop`, `hexists`, `hforall`, `H₁ ⋆ H₂` and `H₁ −∗ H₂`; entailment `H ⊢ H'`.
  Precedences: `↦` 60, `⋆` 55, `−∗` 52 (all above `=`), `⊢` 15.
* **Laws**: `⊢` is a partial order, and antisymmetry gives *equations*:
  `Entails.antisym : H ⊢ H' → H' ⊢ H → H = H'` (SLF's `himpl_antisym`, which needs
  propext and funext as axioms in Coq, is two lambdas here, because an equation of heap
  predicates computes to pointwise `↔`). So `star.comm`, `star.assoc`, `star.emp_l/r`,
  `star.exists_l` are equations of heap predicates; `star.mono_l/r` (the frame property),
  `star.pure_l` (`(\[P] ⋆ H) h ↔ P ∧ H h`), `star.forall_l`; the wand adjunction
  `wand.adjoint : (H₁ ⋆ H₂ ⊢ H₃) ↔ (H₁ ⊢ H₂ −∗ H₃)`, `wand.cancel`, `wand.mono`,
  `wand.frame`; and `pts.same_loc : (l ↦ v) ⋆ (l ↦ w) ⊢ \[False]`.

## 24c: Hoare triples, as a Dijkstra monad ✅

`lib/Hoare.wiz` (`import Hoare`), SLF chapters WPsem and Repr. The presentation is SLF's —
a weakest precondition per command, triples defined from it, structural rules derived —
shaped as an instance of *Dijkstra monads for all* (Maillard, Ahman, Atkey, Martínez,
Hriţcu, Rivas, Tanter, ICFP 2019; "DM4All"), so that other effects can be added by giving
another effect observation, without changing the logic:

| DM4All | here |
|---|---|
| computational monad `M` | `Prog V`: a tree of heap operations `get`/`set`/`alloc`/`free`/`fail` with continuations (a free monad; an *action tree* in the sense of SteelCore, Swamy et al., ICFP 2020) |
| specification monad `W`, ordered (§3.1) | `W V A := (A → HProp V) → HProp V`, `W.ret`, `W.bind` (monad laws by `rfl`), `W.le w₁ w₂ := ∀ Q, w₂ Q ⊢ w₁ Q` (the order of DM4All §3.1, with `⊢` for `⇒`), `W.bind_le` (bind is monotone given a monotone first argument) |
| restriction to monotone transformers (§3.1, §4.1) | `W.Mono`; for separation logic also `W.Frame w := ∀ Q H, w Q ⋆ H ⊢ w (Q ⋆ H)` (SteelCore's `preserves_frame`, at the level of transformers) |
| effect observation (Definition 1) | `wp : Prog V A → W V A`, by SLF's rules (`wp (get l k) Q = ∃v. l ↦ v ⋆ (l ↦ v −∗ wp (k v) Q)`, `wp (alloc v k) Q = ∀l. l ↦ v −∗ wp (k l) Q`, …, `wp fail Q = \[False]`); `wp.ret` by `rfl`, `wp.bind` by induction: a monad morphism. `wp.mono`, `wp.frame`: every `wp c` is in the restricted specification monad |
| `D A w = {c : M A ∣ θ c ≤ w}` | `Triple P c Q := P ⊢ wp c Q`: `c` meets the specification `w Q' := P` (for `Q' ⊇ Q`); `D A w` itself is not built, the examples only need triples |

The rules follow from those properties: `Triple.conseq` (monotonicity),
`Triple.frame` (frame preservation), `Triple.ret`/`Triple.bind` (the morphism laws plus
monotonicity), `Triple.exists`, `Triple.pure`; the small-footprint specifications
`Triple.read/write/ref/dispose`; and the `xapp`-style `wp.get_intro` etc. used in proofs.

**Adequacy.** `Prog.run c h n` interprets a program on a concrete heap whose locations
from `n` on are free (`Heap.Bounded h n`; `alloc` hands out `n`); a fault (unallocated
cell, `fail`) is `none`. `adequacy : Bounded h n → wp c Q h → Post Q (run c h n)`: the
run doesn't fault, ends in a heap satisfying `Q`, and keeps the bound; `Triple.run` adds a
frame. This is what makes `wp` mean something: it is not only a definition.

**Examples.** `Prog.swap_spec : {p ↦ a ⋆ q ↦ b} Prog.swap p q {p ↦ b ⋆ q ↦ a}`, and in-place list
reversal: `MList L p` (cells of two locations, value then next pointer, `0` is null),
`Prog.revLoop.spec` (the loop invariant, by induction on the list) and
`Prog.reverse_spec : {MList L p} Prog.reverse fuel p {r. MList (List.reverse L) r}`. Programs are
total, so the loop takes fuel; the specification asks for more fuel than cells, and since
`wp fail = \[False]` a proved triple also proves the fuel suffices. They were first proved
by explicit rearrangements of `⋆` chains (`star.swap`, `star.assoc_l`, …, about 45 lines);
since 24d they live in `lib/HoareExamples.wiz` and are proved by the tactics (7 lines).

**What is next** (plan S3–S6): see the end of 24d.

## 24d: automation: `xsimpl`, `xpull` and the `x`-tactics ✅

`lib/HoareTactics.wiz` (`import HoareTactics`), SLF chapters Himpl (`xsimpl`) and WPgen
(the `x`-tactics); `lib/HoareExamples.wiz` has the verified programs. Plan S3.

```
def Prog.swap_spec (p q a b : Nat) :
    Triple ((p ↦ a) ⋆ (q ↦ b)) (Prog.swap p q) (fun _ => (p ↦ b) ⋆ (q ↦ a)) := by
  xgo

-- one step of in-place reversal: read and turn the next pointer, then the loop invariant
  | .cons x L, .succ f, h, .succ p, q, L₂ => by
      xstep as n, hp; xstep
      xapp (Prog.revLoop.spec L f h n (Nat.succ p) (.cons x L₂))
```

**Design: small reflection, tactics on top.** The tactics are Wiz functions over the
reflected goal (6c); they decide what to do and build proof terms from a dozen lemmas that
are proved once, so nothing the tactics do is trusted (the kernel checks every term, and a
wrong step is a type error, not a wrong proof). The lemmas are about **star lists**:
`starL [H₁, …, Hₙ]` is definitionally `H₁ ⋆ (… ⋆ Hₙ)`; `starL.pick n Hs` brings the
`n`th element to the front (one lemma by induction on `n`, instead of a chain of
`star.assoc`/`star.comm` per rearrangement), and `HTree.flat_eq` flattens any tree of `⋆`
and `emp` (a reflected `HTree` whose denotation is the goal's side). A reflective
normaliser with a proved cancellation procedure (a decision on index lists) was the
alternative; it was not needed, because the cancellation has to unify anyway (existential
witnesses are metavariables, solved by matching an atom of the other side), which a closed
computation can't do, and the per-step lemmas keep proof terms linear in the number of
steps.

| tactic | does |
|---|---|
| `xsimpl` | flattens both sides; on the left turns `\[P]` into a hypothesis and `∃x` into a variable; on the right gives `∃` a metavariable witness, cancels atoms equal argument by argument up to conversion (solving metavariables), turns `\[P]` into a side goal (closed if reflexivity, an assumption or `fun e => e` proves it), uses `H₁ ⋆ (H₁ −∗ H₂)` on the left, introduces `… ⊢ ∀x. J x` and `… ⊢ H₁ −∗ H₂`, closes `emp ⊢ emp` and `… ⊢ htop`; unfolds representation predicates that compute (`MList (x :: L) p`) when stuck. What is left is a goal, shown as `⋆` chains |
| `xpull` | only the left-side part (`xpull as n, h` names what it introduces) |
| `xwp` | a triple as `P ⊢ wp c Q`, pulled |
| `xstep` | one command of `wp c Q`: `get`/`set`/`free` find the cell in the precondition (unfolding predicates if needed), `alloc` introduces the new location, `ret` leaves `P ⊢ Q v`; through binds |
| `xval`, `xseq` | a returning program, then `xsimpl`; split `c >>= f` |
| `xapp t` | a call, with `t : Triple P c Q'`: splits binds off the front until the program is `c` (`xapp [r, h] t` names the result and its facts), then `xsimpl` on `L ⊢ P ⋆ ∀r. Q' r −∗ Q r` (SLF's `xapp_lemma`): the frame is inferred, and the goal goes on after the call |
| `xchange e`, `xunfold` | rewrite an atom of the precondition with `e : H₁ ⊢ H₂`; unfold every atom that computes |
| `xgo` | `xstep` until a call or the end, then `xsimpl` |

The examples (`lib/HoareExamples.wiz`): swap (`by xgo`), reversal (7 lines instead of about
45), a counter (`incr` by `xgo`; three calls with frames by three `xapp`s; a fresh counter
from `alloc`), the length of a mutable list (read-only traversal, with an accumulator),
adding one to every element in place, and freeing a list (`free`). Every recursive
specification is a `def` by structural recursion with one `by` block per case: the
tactics have no induction (the cases where the precondition is contradictory are one
`xunfold` and an `absurd`).

**What got in the way** (each is a wishful entry):

* Constructor applications are opaque to tactics (`tactic-reflect-constructors`): a list
  literal `.cons x L`, `Nat.succ p` and a program `Prog.get l k` all reflect as handles.
  So goals show star lists as chains (never as `starL [...]`, which couldn't be read
  back), lemmas whose premise is under a binder take the rest of the precondition as one
  predicate, and programs are taken apart by unification with each constructor.
* No tactic request unfolds a definition (`tactic-whnf-unfold`; values are glued, so
  `normalize` keeps names): unfolding is unification with a shape (`hexists ?A ?J`), which
  also leaves the recursive occurrences as raw eliminator terms (`MList L n` comes back as
  `ind … L n`); the loop folds them back by unification with the predicates it unfolded.
  Each failed probe is a failed unification; they stay fast here because they compare
  arguments first (`XT.argsEq`), but see `slow-failing-unification`.
* The term `rfl` is not checked against its equation by the elaborator, only by the
  kernel (`elab-rfl-unchecked`): `def w (r a : Nat) : r = Nat.succ a := rfl` elaborates
  and is rejected by the kernel. A tactic that tries `rfl` (`try rfl`, `first | rfl | …`)
  therefore "closes" any equation; side conditions are tried with `exact XT.refl _`, which
  unifies.
* Variables introduced by unification get generated names (`x7`), so the tactics take
  names (`as n, hp`); `trace` prints nothing (`tactic-trace-output`), so tactics are
  debugged with `fail`.
* `succ b = succ c` computes to `b = c`, so `Eq.congrArg Nat.succ e` has the type of `e`,
  and `Eq.trans e₁ (Eq.congrArg Nat.succ e)` can't infer its middle endpoint
  (`Nat.succ_eq_of` passes the endpoints; the known gap "implicit endpoints of heap
  equations are not inferred" in another form).

Tests: `lake test -- seplogic` (the cases above, the leftover goal of a non-theorem, a
wrong specification left unproved).

**What is next** (plan S3–S6). A `wpgen` (characteristic formulas computed by a
function, SLF chapter WPgen) once tactics can read constructors; an `xif`/`xcase` with
case analysis inside a tactic (needs a `cases` request or motives built from the goal);
a second effect observation from `Eff` (lib/Eff.wiz) state operations into `W` — the
morphism-based shape means this is a translation `Eff [Heap] → Prog` plus its morphism
lemma (watch agent/lin-fixes's one-shot continuations); linear points-to tokens at
quantity 1 over a native heap, with this model as the `implemented_by` reference (CS7b);
then a scheduler semantics, CSL with resource invariants and PCM ghost state (CS10a).
SteelCore's action trees with `Par` nodes are the model for where concurrency goes.
