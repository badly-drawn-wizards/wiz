# Stage 28: solvers

Automated solvers decide goals that are tedious to prove by hand: linear arithmetic side
conditions, Boolean identities, bit-vector facts. Wiz uses them in two ways, which differ
in what is trusted (design and survey: `wiz-notes/smt.md`):

* **`smt`** (28a) asks an SMT solver (Z3) and believes it: an axiom per use, behind a
  flag, as `native_refl` (stage 27) does for compiled evaluation;
* **`sat_decide`** (28b) asks a SAT solver (CaDiCaL) for a *proof*, an LRAT certificate,
  which a checker written in Wiz and proved sound checks in the kernel: nothing new is
  trusted, as with Lean's `bv_decide` (which runs its checker compiled, trusting the
  compiler) or Coq's SMTCoq.

## 28a: `smt` and `--trust-smt` ✅

    def trans (a b c : Nat) (h₁ : Nat.lt a b = .true) (h₂ : Nat.lt b c = .true) :
        Nat.lt a c = .true := by smt
    def nn (x : UIntN 8) (h : Nat.lt (UIntN.toNat x) 256 = .true) :
        UIntN.not (UIntN.not x) = x := by smt

`smt` is a tactic (lib/Prelude.wiz, over the request `Tac.smt`). It is accepted only

* with **`--trust-smt`** (`wiz check/build/run/lsp`, grail), off by default, a flag
  only (not a setting): "SMT solving is not enabled …" otherwise. `--smt-solver CMD`
  (default `z3`) and `--smt-timeout MS` (default 10 000) choose the solver;
* in the body of a `def` (the axiom is named after it).

**How.** The host translates the goal and its context to SMT-LIB 2 (`Wiz/Smt/Translate.lean`),
asserts the hypotheses and the negated goal, and runs the solver
(`Wiz/Smt/Process.lean`: a process call behind an `opaque`, as the module cache does;
answers are kept in `<cache>/smt` under the hash of the solver's identity and the query,
so a check replays without the solver). `unsat`: the goal is closed by a new axiom
**`X.smt✝N⟨z3 5.1.0⟩ : Π ctx, goal`** (the goal over its context, with erased binders,
named after the definition, the use and the solver), applied to the context. `sat`: the
tactic fails with the solver's model, in the user's names. The definition gets a warning;
`#print axioms` lists the axiom, with a note, for it and everything that uses it.

**The fragment.** Propositions (`→`, `¬`, `∧`, `∨`, `↔`, `True`, `False`, equations),
`Bool` (`Bool.and/or/not/xor`, comparisons), `Nat` as integers `≥ 0` (`+ *`, `succ`,
`pred`, `max`, truncated `-`, and `/`, `%` with Wiz's `x / 0 = 0`, `x % 0 = x`), and words
`UIntN w` with a numeral width as `(_ BitVec w)` (arithmetic, bitwise operations, shifts and
`testBit` by numerals, comparisons, `ofNat`, `toNat`). A subterm outside it becomes an
*atom* (a fresh constant; equal terms are the same constant): sound, since a formula valid
for an arbitrary value is valid for this one. Hypotheses outside it are dropped.

**Words need a range hypothesis.** `UIntN w` is a `Nat` whose bound is kept by
construction, not by a proof, so the kernel's `UIntN 8` has values like
`UIntN.ofBitsTrusted 300`, on which the definitions are not bit-vector operations:
`UIntN.not (UIntN.not x) = x` is valid for bit vectors and *false* in Wiz (the kernel
refutes it at 300). A naive translation would make Wiz inconsistent. So `smt` requires
`Nat.lt (UIntN.toNat x) 2^w = .true` for every word variable or atom, and refuses
otherwise. (agent/seal-range makes the bound a proof field of `UIntN`; then the hypothesis
goes.)

**What is trusted**: the solver (named in the axiom), the translation (one Lean file,
reviewed), the process plumbing (only the exact answer `unsat` closes a goal) and the
answer cache (keyed by the whole query and the solver's identity). Not trusted: whatever
built the goal (the axiom's statement is the goal itself, checked by the kernel as a
type). The flag and the solver settings are in the cache keys (commands, modules, grail's
jobs), so an acceptance is never replayed without the flag. `lib/` never uses `smt`
(group *smt* greps it).

**The self-hosted toolchain** has no `smt`: the request is the Lean host's.

## 28b: `sat_decide`: certified, with LRAT ✅

    import SatTactic
    def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide

`#print axioms demorgan`: none. The pieces (lib/Sat.wiz, lib/SatTactic.wiz):

* **An LRAT checker**, `Sat.lratCheck cnf proof`, with literals `Sat.Lit.mk v pos`, a
  clause database as an association list and RUP along the hints (deletions are accepted
  and ignored), and its **soundness theorem**
  `Sat.lratCheck_sound : lratCheck cnf proof = .true → ∀ τ, Cnf.eval τ cnf = .true → False`
  (invariant: an assignment that satisfies the database satisfies each added clause).
* **Formulas and the Tseitin translation**: `Sat.BForm` (variables, constants, `not and
  or xor iff`) and a circuit of nodes `mk id t a b`, one per distinct subformula. A node's
  variable stands for its subformula, so the satisfying assignment in the proof is just
  "evaluate it" (no fresh-name bookkeeping): `Sat.decide_sound : IsTrue (checkAll f nodes
  out proof) → ∀ σ, BForm.eval σ f = .true`, where `checkAll` checks the nodes' ids and
  runs the LRAT checker on the circuit's clauses plus the negated output.
* **The tactic** introduces the goal's `∀`s, reads `e = .true` or `e₁ = e₂` at `Bool`
  (`TacticM.eqView`: equations are opaque to `Expr`), reflects `e` (other Bool subterms
  are atoms, `σ := Sat.envOf [t₀, …]`), builds the circuit, asks the SAT solver
  (`TacticM.satSolve`: DIMACS out, LRAT back; `--sat-solver CMD`, default `cadical`) and
  closes the goal with `Sat.decide_sound f nodes out proof Sat.trivial σ`. The kernel
  checks `Sat.trivial : IsTrue .true` against `IsTrue (checkAll …)` by running the checker,
  and `BForm.eval σ f = .true` against the goal by conversion. A model is shown as a
  counterexample.

**Trusted**: nothing new. The solver, the tactic, the DIMACS/LRAT plumbing can only make
`sat_decide` fail. The kernel runs the checker, which is slow for big proofs (kernel
evaluation); `native_refl` could run the same check compiled (bv_decide's trust), not
done yet.

**Limits of the prototype.** Reflection follows the goal as a tree, so a circuit with
fan-out written as nested calls (`maj` uses the carry twice) grows exponentially once
unfolded: an 8-bit carry chain checks, a 16-bit one goes over 2 GB. The fix is to reflect
shared subterms (`let`s, or a circuit given as nodes, as the HDL builds them) as one node
each. A stuck `a && b` is a `match`, not `Bool.and`, so it is an atom (write `Bool.and`).

**Not yet**: bit vectors. Bit-blasting `UIntN w` operations into circuits is easy; the
correctness proof needs lemmas such as `testBit (land a b) i = testBit a i && testBit b i`
and the range invariant (28a), which the library does not have yet.
