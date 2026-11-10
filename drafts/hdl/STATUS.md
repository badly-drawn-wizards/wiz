# HDL drafts: status

Optimistic Wiz for the Clash-style HDL (`/workspace/wiz-notes/hdl-plan.md`), written against
the planned surface. Check a file with (through `heavy`):

    .lake/build/bin/wiz check -I drafts/hdl drafts/hdl/<File>.wiz

Import chain: `Shim` ← `Bits` ← `Signal` ← {`Counter`, `Fir`, `Uart`, `Cpu`, `Synth`} ← `Staged`.
An error in an imported file makes every importer exit 1 ("module X has errors"); the
importer's own definitions are still checked. Wishful entries are in
`/workspace/wiz-notes/wishful/<slug>.md`; uses are marked `-- wishful: <slug>`.

Principle: where a workaround spells the *same user-facing surface* (a library body, a
shim for a library another agent is writing), the draft uses it so the rest checks; where
the surface itself needs the feature (numerals, `deriving`, `Signal.fix`, staging), the
draft writes the wanted code and fails there.

Checked at solutions a7e6aa7 (agent/small-fixes). `register` is the plain non-recursive
copattern (copattern-cocon: done). **Drift fixed (2026-11-10):** `Shim` no longer
redeclares the Prelude's Nat operations (`div`, `mod`, `pow`, `testBit`, shifts, bitwise)
or `Bool.xor`, and takes `Vec`/`Fin` from lib/Vec.wiz (keeping only `nthD`, `setD`,
`iterate`, `indices`, `#v[…]`); `Bits` builds on lib/BitVec.wiz (`BitVec n := UIntN n`)
and keeps only Clash's names (`eq`, `append`/`+++`, `slice`), shifts by a bit vector and
the reductions. Callers follow lib's argument orders (`Vec.replicate n x`,
`BitVec.getBit a i`). The BitPack instances for ×/Option/Vec and `BitPack.ofIso` pass
their instance arguments explicitly (`@BitPack.pack A ia …`): with the instance a meta,
unifying its width with `bitWidth A ()` is outside the pattern fragment. With
lib/Hdl/Core.wiz from agent/hdl-s0, `Core` checks and hdl-s0's `Synth.wiz` checks (exits 1
only through Bits).

| File | Status | Remaining errors → wishful entry |
|---|---|---|
| Shim.wiz | checks | — (stand-ins: `if`/`&&` prelude-if-bool-ops; Add/Sub/…/OfNat numeric-classes-bitvec; Functor/Applicative prelude-functor-applicative; `Int` prelude-int; `Nat.clog2`; Vec extras by `Nat` index; `#v[…]` vec-literal, works) |
| Bits.wiz | checks except 2 defs | `u8sum`, `s8neg` (numerals at Unsigned/Signed) → numeric-classes-bitvec. BitPack laws for ×/Option/Vec/Fin are axioms → nat-arith-proofs |
| Signal.wiz | checks except `crossDomain` | `crossDomain` is now rejected, as intended (phantom parameters, PR #10); exits 1 through Bits too |
| Counter.wiz | `counterN` + its sample check | `counter`, `counterER` → numeric-classes-bitvec; `counterFix` → sized-signal-fix; `counter_at` is an axiom → nat-arith-proofs |
| Fir.wiz | `Vec.dot`, `window`, `fir`, `firM` check | `fir4`, `smooth` → numeric-classes-bitvec (+ prefix minus: prelude-int) |
| Uart.wiz | types, hand-written BitPack instances, `BitPack.ofIso` check | `deriving instance BitPack for …` ("no deriver for BitPack") → deriving-bitpack; `txStep`, `txInit` → numeric-classes-bitvec (cascade: `uartTx`, the samples) |
| Cpu.wiz | `Instr`, `encode`, `decode`, `Cpu`, `Vec.index/update` check | `deriving instance BitPack` → deriving-bitpack; `attribute [hdl …]` → hdl-commands; `Isa.exec`, `cpu`, `multiply`, `mem0` → numeric-classes-bitvec (cascade: `Isa.step`, `run`) |
| Synth.wiz | checks | (exits 1 only through Bits). Workarounds marked: numerals-in-class-decls, implicit-lambda-binders, projection-functions |
| Staged.wiz | fails throughout, by design | `⇑`, `⟨…⟩`, `~` → hdl-staging-2ltt |

## Simulation results (`#eval`) vs expectations

* Bits: all ten `#eval`s as expected (44, 254, 165, .true, 224, 13, 5, 13, 18, .negSucc 4).
* Signal: register, registerR, unbundle2, unbundleVec (4 5), registerEn as expected.
* Counter: `counterN 2` wraps as expected (0 1 2 3 0 1).
* Fir: the four `#eval`s as expected (1 2 3 4 0 0; 1 3 6 10 10 10, twice; 1 -1 0 0 0 0).
* Synth: `counterC` simulates 0 1 2 3 4 through the value instance; its netlist has 7 nodes and prints Verilog (input width 0 prints as
  `[0:0]`: the emitter needs a zero-width rule).

**Bug, fixed since (the Vec results above are right now): `#eval` of matches on an index-refined `Vec` returned garbage.**
`def Vec.head {A} {0 n} : Vec A (.succ n) → A | .cons x _ => x; #eval Vec.head (Vec.cons 4 Vec.nil)`
prints `.zero` and the interpreter panics "reached an impossible case" (Run.lean:291).
Cause: erasure fails ("cannot erase Vec.head: cannot infer a type for fun x✝ xs✝ => …;
add an annotation", visible with `#erase`) and the global silently becomes the
`unreachable` stub. Affects `Vec.head/tail`, `zipWith`, and anything matching on `(n, v)`
together. agent/vec-lib's uncommitted change to `Wiz/Compiler/Erase.lean` (erase a `cast`
by *checking* its argument against its own type) looks like the fix. Also worth fixing
independently: a definition that fails to erase should be an error at `#eval`, not a
silent stub.

## Elaboration gaps met on the way (all with workarounds in the drafts)

elab-postpone-lambdas (every lambda annotated), trailing-instance-args (`bitWidth A ()`),
ctor-params-from-expected-type (`@BitPack.mk T …`, `BitPack.ofIso T …`),
elab-solve-type-before-body (kernel `refl` tests became `#eval`s), implicit-lambda-binders,
numerals-in-class-decls (numerals and `+` in class field types), projection-functions,
structure-update, private-decls, phantom-parameters. Also: named instances
(`instance foo : …`) don't parse — not needed by the drafts, not recorded.
