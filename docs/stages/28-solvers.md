# Stage 28: solvers

Automated solvers decide goals that are tedious to prove by hand: linear arithmetic side
conditions, Boolean identities, bit-vector facts. Wiz uses them in two ways, which differ
in what is trusted (design and survey: `wiz-notes/smt.md`):

* **`smt`** (28a, a separate PR) asks an SMT solver (Z3) and believes it: an axiom per
  use, behind a flag, as `native_refl` (stage 27) does for compiled evaluation;
* **`sat_decide`** (28b) asks a SAT solver (CaDiCaL) for a *proof*, an LRAT certificate,
  which a checker written in Wiz and proved sound checks in the kernel: nothing new is
  trusted, as with Lean's `bv_decide` (which runs its checker compiled, trusting the
  compiler) or Coq's SMTCoq.

## 28a: `smt` and `--trust-smt` (a separate PR)

The trusted mode (an SMT solver's `unsat` as an axiom per use, behind a flag) is designed
in `wiz-notes/smt.md` §3 and comes in its own PR, after review (`wiz-notes/smt-review.md`).

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
  (`TacticM.satSolve`: DIMACS out, LRAT back; `--sat-solver CMD`, default `cadical`, and
  `--solver-timeout MS`; flags only, so a grail file can't name a program to run;
  answers are kept in `<cache>/smt`, crashes and timeouts not) and
  closes the goal with `Sat.decide_sound f nodes out proof Sat.trivial σ`. The kernel
  checks `Sat.trivial : IsTrue .true` against `IsTrue (checkAll …)` by running the checker,
  and `BForm.eval σ f = .true` against the goal by conversion. A model is shown as a
  counterexample.

**The solver.** Release tarballs ship CaDiCaL in `share/wiz/cc/bin/cadical` (the Lean
toolchain's copy, which Lean ships for `bv_decide`; scripts/bundle-cc.sh), and a bundled
toolchain uses it by default. A checkout finds `cadical` on PATH (the Nix dev shell has
it). Z3 is not shipped (tens of MB, and `smt` is opt-in): the trusted mode's flag will find it.

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
and the range invariant of `UIntN` (agent/seal-range), which the library does not have yet.

## 28c: sharing ✅

    def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)
    def eq4 … : Bool.xor (Bool.xor a3 b3) (carry a2 b2 (carry a1 b1 …)) = Bool.xor … (maj b2 a2 (maj …)) := by sat_decide

28b's formulas are trees: `maj` uses its last argument twice, so a carry chain unfolded is
exponential (a 16-bit one went over 2 GB). Now the goal becomes a **circuit of nodes**
(`Sat.GNode`: a node number and a gate over other nodes), one per distinct subterm, and
**a node's value is the goal's own subterm**: `σ v` is that subterm, so no formula is
ever rebuilt. What the circuit claims is checked by the kernel, node by node:
`Sat.allHold σ nodes` is the conjunction of `σ v = op (σ a) (σ b)`, each proved by `refl`
at the subterm (`Sat.eqRefl`), which the kernel compares with its operands *folded* (both
sides are the same subterms). Then `Sat.dag_sound`: an LRAT refutation of the gates'
clauses and `¬ σ out` gives `σ out = .true`, with no Tseitin bookkeeping at all (the
clauses hold under `σ` itself). No axioms.

* **Head-only unfolding.** An application of a definition (`maj x y z`) is unfolded at
  its head only: the definition applied to variables is unfolded (`TacticM.unfold` under
  `fun`s) and the arguments put back (`TacticM.instantiate`), so they stay folded, and are
  nodes already. A definition that does not unfold to a connective is an input.
* **`TacticM.define`** (a new request): a definition in the goal's context, added before
  the definition being elaborated and checked by the kernel like any other (it is not an
  axiom: `#print axioms` does not list it). The proof uses two, `σ` and the node list,
  instead of repeating them in every node's proof.
