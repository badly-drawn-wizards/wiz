# Libraries

## H0c: vectors and bit vectors ✅

`lib/Vec.wiz` (`import Vec`): `Fin n` (a `Nat` with an erased proof `Nat.lt val n = .true`;
`Fin.of 5 3 rfl`) and `Vec A n`, whose length is an **erased** index: at runtime a
vector is a list, and `Vec.length` counts it, with `Vec.length_eq : Vec.length v = n`.
Functions: `head`/`tail`/`last`/`init` on non-empty vectors, `get`/`set` by `Fin`,
`map`, `zipWith`, `zip`, `foldl`/`foldr`, `replicate`, `ofFn`, `append`, `reverse`
(linear, with a `cast` along `m + (k+1) = (m+k)+1`), `snoc`, `splitAt`, `shiftIn`,
`toList`/`fromList` (`fromList l : Vec A (List.length l)`). Theorems: `length_eq`,
`length_toList`, `toList_fromList`, `map_map`, `get_set` (`get (set v i x) i = x`),
`get_map`, and the `Nat` lemmas they need (`add_zero`, `add_succ`, `add_comm`), all by
structural recursion. `map_map`, `get_set` and `get_map` go through equations such as
`Vec.map_cons : map f (cons x xs) = cons (f x) (map f xs)`, which hold only up to casts at
the element type and are proved with the Prelude's axiom `castRefl` (below).

`lib/BitVec.wiz` (`import BitVec`): `BitVec n` (since [22h](stages/22-numbers.md), `UIntN n` under another name), a `Nat` below `2^n` by construction
(every operation reduces mod `2^n`). Wrapping `add`/`sub`/`neg`/`mul`, `udiv`/`umod`,
`and`/`or`/`xor`/`not`, `shl`/`lshr`/`ashr`, `getBit`, `msb`, `beq`/`ult`/`ule`/`slt`/`sle`,
`concat`, `extract hi lo`, `zeroExtend`, `signExtend`, and `toVec`/`ofVec` (to and
from `Vec Bool n`, least significant bit first). Operations that need `2^n` take the
width at runtime (`{ω n : Nat}`). The arithmetic is the Prelude's native `Nat`
operations ([22a](stages/22-numbers.md)), so the kernel computes on literal bit vectors:
`(BitVec.add (BitVec.ofNat 8 200) (BitVec.ofNat 8 100)).toNat = 44 := rfl`. Compiled code
runs `lib/Word.wiz`'s native words ([22h](stages/22-numbers.md)).

Along the way the elaborator learned to:
* keep erased constructor fields and arguments erased when a `match` reverts them, and
  name a field directly instead of through a `let` at ω (`| .mk i h => … h …` with
  `0 h`);
* prove an equation that has already computed with `rfl` (`Nat.succ a = Nat.succ a`
  is a Σ of `True`s and `a = a`), and recompute an equation stuck on a metavariable
  once it is solved (`congrArg Nat.succ ih` against such a goal). The proof follows the
  elaborator's computed form; where the kernel computes the equation to another shape
  (a numeral on one side, a constructor on the other), the kernel rejects it;
* erase a `cast` against its source type (the solution rule casts a function, so
  `head`, `tail` and `zipWith` on vectors failed at runtime).

Not yet: facts like `Vec.get v (Fin.of 3 1 rfl) = 20 := rfl` (the `rfl` shape
problem above; `drafts/vec-lib/VecProofs.wiz`), arithmetic facts about `BitVec` in general, numerals and operators
(`a + b`) for `BitVec` (decision HD9).

## H14 S0: hardware as tagless-final code, with sharing ✅

`lib/Hdl/Core.wiz` (`import Hdl.Core`) is the L2 layer of the HDL plan: combinational
logic is code polymorphic in its representation, `{r : HwTy → Type} → [Hw r] → r a → r b`,
over hardware type codes `HwTy` (`bits n`, `prod a b`). `Hw` has the operations (`lit`,
`add`, `sub`, `mul`, `and`, `or`, `xor`, `not`, `eq`, `ult`, `mux`, `cat`, `slice`, `pair`,
`fst`, `snd`, `share`); such code can only combine wires with them, so it is synthesisable
by construction. Two instances: `HwTy.El` (values: simulation) and `Wire` (a netlist
builder). A `Circuit i o` is a Mealy machine whose step is such code: `Circuit.run`
simulates it on values, `Circuit.netlist` builds its netlist, `Netlist.simulate` runs the
netlist, and `Verilog.emit` prints Verilog-2005. The module declares its registers (with sized initial
values), then one wire per node, then the register updates, so every name is declared
before its use (Icarus Verilog insists; the `hdl` test group runs it when it is installed). `examples/hdl.wiz` has a counter, a
saturating counter, a popcount, a 4-tap sum and a doubling chain.

Sharing has two parts:
* the netlist builder **hash-conses**: emitting a node whose operation, width and
  arguments (sorted, for commutative operations) are already present returns the existing
  node, so identical subterms are one node however they were reached;
* **auto-share**: in check mode, a `let x := v; body` with no explicit quantity becomes
  `ShareLet.share v (fun x => body)` when the class `ShareLet` is declared and an instance
  `ShareLet A B` exists for the value's type `A` and the body's type `B`. `Hdl.Core`'s one
  instance is `[Hw r] → ShareLet (r a) (r b)` (through `Hw.share`), so a meta-level `let`
  of an object value names one wire: the doubling chain `let y := x + x` at depth 20
  emits 20 adders in 25 builder steps. Write `let ω x := …` to opt out.

## H14 S1: a usable HDL: names, bundles, composition, reset, emitters ✅

Driven by a real design (a UART on a Lattice iCEstick, written in this library and run on
the board; its findings G1–G10 are the requirements). Design notes:
`/workspace/wiz-notes/hdl-usability.md`. Everything is in `lib/Hdl/Core.wiz`; examples and
tests in `examples/hdl-compose.wiz` (group `hdl`) and in the `scaling` group.

```
structure Tx (r : HwTy → Type) where      -- a bundle: a structure of signals
  line : r Bit
  left : r B4
  deriving Bundle                         -- Tx.code, Tx.pack, Tx.unpack, Tx.bundle
def txStep {r : HwTy → Type} [Hw r] (s : Tx r) (go : r Bit) : r Tx.code :=
  let idle := Hw.eq s.left (Hw.lit 4 0);  -- field access by name
  Tx.pack (Tx.mk (Hw.mux go (Hw.lit 1 0) s.line) (Hw.label "left" …))
def top : Circuit In.code Out.code := Circuit.bundled Tx.bundle In.bundle Out.bundle init topStep
-- module top(input clk, input [0:0] rx, output [0:0] tx, output [4:0] leds); reg … line; reg … left;
```

* **Structured wires.** `Wire t` is a product of node ids, one per leaf of `t`: pairs and
  projections emit nothing, `mux` at a product is one multiplexer per leaf. A code may
  carry names, `HwTy.named s t` (ignored by `El`, `width` and the bus encoding). Ports
  and registers are one per leaf, named by the path of `named` segments joined with `_`
  (`HwTy.portNames`; an unnamed leaf is `x`/`y`/`r`, with `_k` where names would clash);
  wires are named by `Hw.label "name" x`, others are `nK`. Verilog names are sanitised
  and unique. `Hw` gained `const`, `tag`/`untag`, `label`, `resetTo`, `hold`.
* **Bundles.** A structure parameterised by `r : HwTy → Type` with fields `r T` or nested
  bundles; `deriving Bundle` defines its code (a product of `named` fields) and the
  conversions. The code's tails are definitions too (`S.code := HwTy.prod (named "f₀" T₀)
  S.code.tail1`, …), `pack` ascribes each rest its tail's name and `unpack` walks the
  product with one `let` per field, so the code of both is linear in the number of fields
  (it was quadratic and cubic). (Reading field k of a structure is still k projections in
  the IR, so `pack` of a wide bundle has a quadratic number of projections.) A bundle is a *value* (`S.bundle`), not an instance: structures are
  structural types, so two structures with the same field types are one type and
  instance resolution could not tell their bundles apart (instances once declared types get
  kernel-level brands).
* **Composition** (Lava/Clash-style arrows): `Circuit.comb`, `delay`, `seq`, `par`,
  `loop` (feedback through a register), `named` (names the state), `mapIn`/`mapOut`,
  `inputName`/`outputName`, and `Circuit.inst c s x` for an instance with its own state
  inside a hand-written step. Each has its semantics as a lemma: `Circuit.runFrom_seq`,
  `run_seq` (`run (seq a b) xs = run b (run a xs)`), `run_par`, `run_delay`,
  `runFrom_loop`, `run_named`, `runFrom_comb`, `inst_el`, `stepEl_withReset`/`Enable`.
  Combinational code passed to a combinator is a function at every representation,
  `Comb i o := {r : HwTy → Type} → [Hw r] → r i → r o` (`Circuit.comb (fun x => Hw.xor x k)`),
  and a bundled step is such a function on structures (`Circuit.bundled … cntStep`).
  The netlist is flat.
* **Reset and enable**, by construction: `Circuit.withReset c` adds an input `rst` (while
  high, the next state is `c.init`: synchronous) and `withEnable` an input `en` (while low,
  the state holds), built from `Hw.resetTo`/`Hw.hold`, whose meaning at values is a
  multiplexer and which the netlist turns into a reset or enable of the register they
  feed: `always @(posedge clk) if (rst) r <= 4'd0; else if (en) r <= next;`. Where the
  pattern does not apply (a `resetTo` not feeding a register), the node stays a
  multiplexer with the same meaning. `initial` values are always printed.
* **Emitters.** `Testbench.verilog n vec cycles` (a bench that replays a vector file and
  compares every output in every cycle), `Circuit.vectors n c xs` (the vector file of a
  value simulation), `Vcd.ofRun name c xs` (a waveform of every input, output and state
  leaf), `Pcf.emit n clkPin pins` and `Pcf.check` (pin constraints from named ports:
  `Pin.one "uart_tx" 8`, `Pin.bus "leds" [99, 98, …]`).
* **Designs in a list.** `Circuit i o` quantifies over representations and lives in
  `Type 1`; `Circuit.design name c : Design` packs a top at the first order (the step at
  values and the netlist), so `List Design` works.
* **Simulation scales.** `Circuit.run` is tail recursive (`Circuit.run_eq` relates it to
  the structural `Circuit.runFrom`, the one to reason with); `Netlist.simulate` keeps node
  values in a skew-binary random-access list: O(n log n) per cycle instead of O(n²).
* **Names.** The generic helpers are `Hdl.map`, `Hdl.nthD`, `Hdl.rev`, `Hdl.show`, …
  (importers keep `List.map` and the like); the netlist types are `NetOp`, `NetNode`,
  `NetReg`, `NetPort`. (`<+>` stays.)

Not done: module hierarchy in the Verilog, enumerations at `HwTy`, wire names from `let`
binders (an elaborator hook, wishful `hdl-let-names`), asynchronous reset, several clocks.
(Numerals and operators: H14 S2.)

## H14 S2: operator notation for signals ✅

Signals are written with operators: `c + 1`, `x &&& ~~~y`, `s.left === 0`,
`if go then 10 else if tick then s.left - 1 else s.left`, instead of
`Hw.add c (Hw.lit 7 1)` …, `Hw.mux go (Hw.lit 4 10) (Hw.mux tick …)`.
`examples/hdl-operators.wiz` shows each design both ways.

| notation (at `r (HwTy.bits n)`, `[Hw r]`) | meaning | precedence |
|---|---|---|
| numeral `k` | `Hw.lit n k`: the width from the type | |
| `a + b`, `a - b`, `a * b`, `-a` | `Hw.add`, `Hw.sub`, `Hw.mul`, `0 - a` | 65, 65, 70, 75 |
| `a &&& b`, `a ^^^ b`, `a \|\|\| b`, `~~~a` | `Hw.and`, `Hw.xor`, `Hw.or`, `Hw.not` | 60, 58, 55, max |
| `a <<< k`, `a >>> k` (`k : Nat`) | logical shifts by a fixed number of places: wiring (`Hw.shl`, `Hw.lshr`) | 75 |
| `a <ᵤ b`, `a ≤ᵤ b`, `a >ᵤ b`, `a ≥ᵤ b` | unsigned comparisons, one bit (`Hw.ult`, `Hw.ule`, `Hw.ugt`, `Hw.uge`) | 62 |
| `a === b`, `a =/= b` | equality, inequality, one bit (`Hw.eq`, `Hw.neq`) | 61 |
| `if c then a else b` (`c : r HwTy.bit`) | `Hw.mux c a b`, at any `r t` | |

* **Classes.** `+ - * -x` and numerals are the numeric classes (`Add` … `OfNat`, HD9).
  The bitwise operators are new classes in the prelude, as in Lean: `AndOp`, `OrOp`,
  `XorOp`, `Complement`, `ShiftLeft`, `ShiftRight`, with instances for `Nat`, `UIntN w`
  (and so `BitVec n`) and signals. The shifts take the amount as a `Nat`: a fixed amount
  is what hardware shifts by wiring (a concatenation with `k` zeros and a slice; no
  shifter; by `n` or more places, `0`).
* **Comparisons are the HDL's own.** They return a 1-bit signal, not a `Bool`, so they are
  not `==`/`<` (Chisel makes the same choice: `===`, `=/=`), and they are unsigned (`ᵤ`,
  leaving room for signed ones). As in Verilog they bind tighter than the bitwise
  operators: `idle &&& s.cnt === 9` needs no parentheses.
* **`if` on a signal.** `if c then a else b` is a `match` on a `Bool` (13c). When the
  condition's type is not a data type and has an instance `Mux C C` (the prelude's class
  `Mux C A`, whose HDL instance is `Mux (r HwTy.bit) (r t)`), the elaborator makes it
  `Mux.mux c a b` instead (`ifMux?` in `Wiz/Elab/Term.lean`), at an instance `Mux C A`
  for the branches' type `A`. Every other condition (a `Bool`, an unsolved type, `Nat`, a
  type without a `Mux` instance) takes the ordinary path, with its messages, and
  `if b then rfl else rfl` still refines the goal. A branch that is a numeral (or an `if`
  of numerals) is elaborated after the other, so `if t then 0 else c + 1` gets its width
  from `c`.
* **Constants of the expected width.** A numeral is a literal; a meta-level `Nat`
  expression is `Hw.ofNat e` (`c === Hw.ofNat (n - 1)`), whose width comes from the type.
* **Same circuits.** The instances are the `Hw` operations, so a circuit written with the
  operators has the netlist and the Verilog of the one written with `Hw.add` …, byte for
  byte (`examples/hdl-operators.wiz`; also the iCEstick UART's `txStep` and `rxStep`
  rewritten). Associativity matters for that: `a &&& b &&& c` is `(a &&& b) &&& c`, a
  different (equivalent) netlist from `Hw.and a (Hw.and b c)`.
* **Printing.** The operators print back as written (11r): `fun x y => if x === y then
  x + 1 else x <<< 2 &&& ~~~y`. `Mux.mux` and `Hw.mux` print as `if`; and a numeral at any
  type other than `Nat` (`OfNat.ofNat A n _`) now prints as the numeral, for `Int` and
  words too (`fun x => x + 1 : Int → Int`).

Not done: ASCII spellings of `≤ᵤ` …. (Shifts by a signal, signed comparisons, arithmetic
shift and `&&`/`||` on signals: H14 S4.)

## H14 T: temporal properties of circuits (prototype)

Stating and proving properties of circuits over unbounded time, after TLA+, LTL and
SVA. `lib/Hdl/Temporal.wiz`, on the traces and Mealy machines of H14 C1 (`lib/Trace.wiz`);
examples and tests in `examples/hdl-temporal.wiz` (group `hdl`). Survey and design:
`/workspace/wiz-notes/hdl-temporal.md`.

```
def Uart.onlyThat_a5 :     -- the loopback reports byte 0xa5 and nothing else, for ever
    TL.always (TL.nowB (fun o => onlyByte 165 o.1 o.2)) (Mealy.obs loopM loopback.init (sendOnce 165)) 0 :=
  Mealy.always_settled_const loopM (onlyByte 165) loopback.init (sendOnce 165) quiet F (loopIdle 165)
    (sendOnce_from 165) (refl Bool.true) (refl (loopIdle 165)) (loopIdle_fixed 165) (loopIdle_ok 165)
```

* **Formulas** `TL A := Trace A → Nat → Prop`: a proposition about a trace at a cycle.
  `TL.always φ σ t := ∀ k, φ σ (k + t)`, `TL.eventually` its `∃` (traces are functions, so
  □ is a Π and ◇ an impredicative `∃`, not ν and μ).
* **Operators**: `now`/`nowB` (atoms), `and`/`or`/`imp`/`not`, `next` (○), `nexts n`
  (`##n`), `within n` and `during n` (bounded ◇ and □), `delayRange m n` (`##[m:n]`),
  `until`, `implies`/`impliesNext` (`|->`/`|=>` for a Boolean antecedent), `past n`
  (`$past`), and TLA's `leadsTo`, `infOften`, `WF`, `SF`, `act` and `stut` (`[R]_v`).
* **Laws**: `always_now`, `always_next`, `always_cons`, `always_ind` (induction on time),
  `always_of`, `always_mono`, `always_and`, `always_during`, `eventually_now`,
  `eventually_next`, `eventually_mono`, `within_eventually`, `splitTime`/`splitAt` (a
  transient phase, then the rest).
* **Proof rules** (with `Mealy.invariant` and `Mealy.simulates` from H14 C1):
  `Mealy.refinesStut` (TLA refinement up to stuttering), `TL.fairStep` (liveness from a
  fair Boolean event: WF1), `TL.rank` (liveness with a bound from a ranking function),
  `Mealy.settles`, `always_settled` and `always_settled_const` (the run reaches a state
  that is fixed under the remaining inputs; the facts are named, `Mealy.Reaches`,
  `Mealy.Fixed`, `Trace.From`, so that concrete instances are matched by name).
* **Bounded checks by evaluation**: `Mealy.checkFrom`/`findFrom` (one pass over a run)
  with `_spec`, `checkFrom_during`, `findFrom_within`: `refl Bool.true` (the kernel
  evaluates) becomes a temporal statement. For long checks, `native_refl` (stage 27a).

The examples: the UART transmitter's line is high whenever it is idle, at every cycle;
the loopback delivers the byte sent within 45 cycles and reports no other, for ever
(per byte: 48 evaluated cycles and a fixed point); a valid/ready buffer refines a
Bool-level specification for every input trace (eight cases of the control bits, data
variables), keeps an offered item stable (AXI), and hands on every accepted item if the
consumer is ready infinitely often.

Not done: sequences with repetition (SEREs; planned as monitor circuits), stuttering
invariance as a theorem, a deep embedding printable as SVA, notation (□, ◇, `|->`:
dsl-ergo, stacked on this), case splits on neutral bits (they need the range of `UIntN` in
the sealed type; wishful `uintn-range-proof`), a tactic for the Bool case splits.

## H14 C1: traces, the common semantics (`lib/Trace.wiz`) ✅

One semantics for everything that runs step by step (design:
`/workspace/wiz-notes/cohesion-hardware.md`, 2.1). A trace is a function, `Trace A :=
Nat → A` (equality is pointwise and computes; a ν-stream's is stuck), and a Mealy machine
is a step `Mealy S I O := S → I → S × O`, run along an input trace by
`Mealy.stateAt m s0 xs t` and `Mealy.outAt`. `Mealy.run` is the finite run on a list and
`Mealy.run_take` says it is a prefix of the infinite one. Proof rules on the trace:
`Mealy.invariant` (an inductive invariant under an environment assumption) and
`Mealy.simulates`/`simulatesOut` (refinement by a representation map, one step as the
premise). `Trace.tail`, `map`, `zip`, `cons`, `const`, `once`, `ofList`, `take`.

A circuit is such a machine: `Circuit.mealy c` (its step at values),
`Circuit.trace c xs : Trace (El o)`, `Circuit.stateAt`, `Circuit.obs` (state and input
per cycle, what temporal formulas are about), and `Circuit.run_take`:
`Circuit.run c (Trace.take n xs) = Trace.take n (Circuit.trace c xs)`, so what a
simulation prints is what a theorem about the trace says. The temporal logic (H14 T)
builds on these.

## H14 C2: lenses for structures and bundles (`lib/OpticDerive.wiz`, `lib/Hdl/Optic.wiz`) ✅

`deriving Lens` gives every field of a structure a lens (lib/Optic.wiz's `Lens S A`), its
laws and the independence of every two distinct fields, all by `rfl`:
`S.fL : Lens (S Δ) T`, `S.fL_lawful : Lens.Lawful S.fL`, `S.f_g_indep : Lens.Indep S.fL
S.gL` (f declared before g; `Hdl.indep_symm` turns it round). The names and statements
are the ones Feral's lowering of `struct` writes, so lowered code can switch to the
deriver. On an HDL bundle (`deriving Bundle, Lens`) a lens is polymorphic in the
representation, `Tx.leftL : Lens (Tx r) (r B4)`: the same lens updates values in a proof
and wires in synthesis. `Hdl.zoom l g` runs a sub-step `g` on the place `l` of a state
(`Hdl.zoom_get`), and `Hdl.zoom_frame` is the frame rule: a place independent of `l` is
unchanged, for every state (no evaluation needed). `Bundle.lens b` (with
`Bundle.Lawful b`, `rfl` for derived bundles) and `HwTy.fstL`/`sndL` are the packed
views at values. Example: `examples/hdl-optic.wiz` (group `hdl`).

## H14 S3: fast simulation for compiled programs (`import Hdl.Sim`) ✅

Compiled, the value simulation (`Circuit.run`, `Design.runLeaves`) runs the step function
at `HwTy.El` every cycle, and with it every meta-level computation the step contains:
table trees and top-level constants (compiled code does not cache a closed top-level
definition: each use computes it again), widths and constants computed from the
configuration, bundle codes, `pack`/`unpack`, and a dictionary call and a closure per
operation. Profiled on the iCEstick OLED demo (`oled_fast`, 1068 netlist nodes, about
1400 cycles/s): about 60% of the time is allocation and reference counting, and the
table trees (`RomT.go`, `List.take`) are rebuilt in every cycle. `Netlist.simulate` is no
faster (an allocation per node in its random-access list).

`lib/Hdl/Sim.wiz` runs the netlist instead: synthesis is the partial evaluation (all the
meta-level work is done once, and the netlist is hash-consed), and the netlist is turned
once into a flat program (a constructor per node with exactly its operands, constants
written once, input ports and register outputs as slots) that runs over native arrays
updated in place (`Array`, lib/Std.wiz).

* `Netlist.simFast n xs` computes exactly what `Netlist.simulate n xs` computes (the same
  formulas on the same numbers, node by node) for every well-formed netlist
  (`Netlist.wellFormed`: arguments refer to earlier nodes, register reads to registers,
  register inputs and outputs to nodes; every netlist `Circuit.netlist` builds), and is
  `Netlist.simulate` on any other.
* `Circuit.simFast c xs` = `Circuit.runLeaves c xs`, `Design.simFast d xs` =
  `Design.runLeaves d xs`, by the netlist's agreement with the values (which the `hdl`
  group and a design's own check, such as `oled gen`'s, establish).
* Compiled code only: `Array` has no definition the kernel or `#eval` could run.
* About 25× the value simulation on `oled_fast` (about 35000 cycles/s) and 13× on
  `examples/hdl-sim-bench.wiz` (informal numbers; `bench/hdl-sim` in wiz-tools times it).
  `examples/hdl-sim.wiz` (the `hdl` group) checks `simFast` against `Netlist.simulate`
  (hash-consed and naive netlists) and `Circuit.run` on every operation, 70-bit widths,
  reset and enable, a table tree and composition, and the fallback.

Not done: skipping nodes whose arguments did not change (event-driven simulation),
generated C for a netlist, a value simulation that keeps its meta-level work (caching
closed top-level definitions in compiled code would remove the table rebuilding).

## H14 S4: the iCEstick gaps: shifts by a signal, signed operations, `&&`/`||`, BitPack, reset and enable ✅

What the iCEstick projects (`/workspace/wiz-icestick-uart`, FINDINGS.md) still had to
work around after S1 and S2. Everything is in `lib/Hdl/Core.wiz`; the examples and tests
are `examples/hdl-gaps.wiz` (group `hdl`, with Icarus Verilog test benches when
`iverilog` is installed) and a shifter in `examples/hdl-sim.wiz` (S3's fast simulation).

| notation (at `r (HwTy.bits n)`) | meaning | Verilog |
|---|---|---|
| `a <<< s`, `a >>> s` (`s : r (HwTy.bits m)`) | logical shifts by a signal (`Hw.shlBy`, `Hw.lshrBy`) | `a << s`, `a >> s` |
| `a >>>ₛ s` | arithmetic shift right by a signal (`Hw.ashrBy`) | `$signed(a) >>> s` |
| `a >>>ₛ k` (`k : Nat`) | arithmetic shift right by a fixed amount: wiring (`Hw.ashr`) | |
| `a <ₛ b`, `a ≤ₛ b`, `a >ₛ b`, `a ≥ₛ b` | signed (two's complement) comparisons, one bit (`Hw.slt`, `sle`, `sgt`, `sge`) | `$signed(a) < $signed(b)` |
| `a && b`, `a \|\| b` (`a b : r HwTy.bit`) | `a &&& b`, `a \|\|\| b` | `&`, `\|` |

* **Shifts by a signal** are four new `Hw` operations (`shlBy`, `lshrBy`, `ashrBy`, `slt`)
  and four new `NetOp`s (`shl`, `lshr`, `ashr`, `slt`; codes 20–23, leaving 17–19 to
  memories, H14 C3). The values (`HwTy.El`), the netlist simulation and `Hdl.Sim` all
  compute them with one set of functions on numbers (`Hdl.shlN`, `lshrN`, `ashrN`,
  `sltN`), and an amount of `n` or more gives 0 (or all sign bits) without computing
  `2^s`. `examples/hdl-gaps.wiz` checks the values against lib/BitVec.wiz's own
  `BitVec.shl`/`lshr`/`ashr`/`slt`/`sle` (every 8-bit value and amount), and the
  Verilog with a test bench that replays the value simulation in Icarus Verilog.
* **The shift notation takes any amount type.** `<<<` and `>>>` are now the prelude's
  `HShiftLeft A B`/`HShiftRight A B` (Lean's `HShiftLeft` without its result type), with
  `HShiftLeft A Nat` from every `ShiftLeft A`, so `Nat`, words and the fixed shifts of S2
  are unchanged, and the HDL adds `HShiftLeft (r (bits n)) (r (bits m))`. A numeral amount
  is a `Nat` (the default type of a numeral), so `x <<< 2` is still wiring.
  `>>>ₛ` is the HDL's class `AShiftRight A B` (signals only).
* **`&&` and `||` on one-bit signals.** The prelude's `a && b` is
  `if a then b else Bool.false` and `a || b` is `if a then Bool.true else b`. When `a` is a
  signal (S2's `if`-as-a-mux test), the elaborator (`ifMux?`) makes them the gates
  `AndOp.and a b` / `OrOp.or a b` at the condition's type, so they print as `&&&`/`|||`
  and have the Verilog of those. On `Bool` they are unchanged (`!` is still `Bool.not`
  only: use `~~~` on a signal).
* **`deriving BitPack`.** `structure BitPack A` is a type's values as bit vectors of one
  width (a value, not an instance, as `Bundle`). For an **enumeration** (no parameters,
  constructors without fields) constructor `i` is the number `i` in
  `⌈log₂ #constructors⌉` bits (Clash's encoding):
  ```
  inductive Phase where | idle | start | data | stop  deriving BitPack
  -- Phase.width = 2, Phase.code = HwTy.bits 2, Phase.toNat, Phase.ofNat (out of range:
  -- the first constructor), Phase.pack : Phase → HwTy.El Phase.code, Phase.unpack,
  -- Phase.unpack_pack : Phase.unpack (Phase.pack p) = p (by cases), Phase.bitPack,
  -- Phase.lit p : r Phase.code (the constant in a circuit: `s.ph === Phase.lit .stop`)
  ```
  A bundle's field can be `r Phase.code`. For a **bundle** `S Δ r` it adds `S.width`,
  `S.toBits : S Δ r → r (HwTy.bits (S.width Δ))` and `S.ofBits` (the bundle as one bus:
  `Hw.packBits`/`Hw.unpackBits`, first field in the high bits as `HwTy.pack`; wiring
  only), `S.unpack_pack : S.unpack (S.pack s) = s` at values and `S.bitPack`; it derives
  the `Bundle` too when `S.code` does not exist yet (`deriving Bundle, BitPack` or just
  `deriving BitPack`). The bit-level round trip `S.ofBits (S.toBits s) = s` holds by `rfl`
  for closed values (the example checks one, and all 32 values of a 5-bit bundle); a
  general lemma needs words' range proofs (stage 22l) and lemmas on `concat`/`slice`.
* **Reset and enable: the convention.** A design with a reset or a clock enable takes
  them as its first inputs, named `rst` and `en`, reset first: both synchronous and
  active high, and the reset wins over the enable, as
  `always @(posedge clk) if (rst) r <= init; else if (en) r <= next;`. Three ways to get
  it, all of which the netlist turns into the register's reset and enable (not
  multiplexers):
  * a whole circuit: `Circuit.withResetEnable c` (= `withReset (withEnable c)`; S1's
    `withReset`, `withEnable` alone);
  * one register: `Circuit.registerR t init`, `registerE`, `registerRE` (a `delay` with
    them; `Circuit.stepEl_registerRE` … say what they do in a cycle);
  * a field of a state, inside a step function: `Hw.regNext rst en init cur next`
    (`init` under `rst`, else `next` under `en`, else `cur`). The netlist sees the reset
    when `init` is the register's initial value, and the enable when `cur` is the
    register itself; otherwise it is the same multiplexers, with the same meaning.

  Every register keeps its `initial` value, which is all an iCE40 needs (yosys turns a
  non-zero initial value into inverters around a flip-flop); a reset is for targets
  without initial values and for restarting a design.

Not done: a general bit-level round-trip lemma for bundles (above), `BitPack` for
inductive types with fields (a tag and the widest constructor's fields), `!` on signals,
`match` on an enumeration signal (staged `match`, hdl-staging-research S3), asynchronous
reset.

## Logic, heap predicates and Hoare triples ✅

`lib/Logic.wiz` (`∧`, `∨`, `∃` with binder notation `∃ x : A, P`, `↔`, `¬`, ASCII
`/\`, `\/`, `exists`, `<->`, equality lemmas, `funext`, `propext`; [13e](stages/13-language.md)),
`lib/HProp.wiz` (model heaps, `emp`, `↦`, `⋆`, `−∗`, entailment and the separation-logic
laws), `lib/Hoare.wiz` (`wp`, triples, the frame rule, adequacy for an interpreter),
`lib/HoareTactics.wiz` (SLF-style automation: `xsimpl`, `xpull`, `xstep`, `xapp`, …) and
`lib/HoareExamples.wiz` (verified swap, list reversal, counter, list length, in-place map,
freeing a list). See [stage 24](stages/24-separation-logic.md).

`lib/HeapBorrow.wiz` is the bridge to Feral's functional model: a `&mut`/`&` borrow of a
heap cell (`Prog.borrowMut`, `Prog.borrowMut2`, `Prog.borrowShr`: read the cell, run the
value-level function, write the final value back), whose triples follow from the
function's `Result.Holds` specification (`Prog.borrowMut_spec`, …) or from its computed
result (`Prog.handBack_ok`, `Prog.handBack2_ok`, for `xapp`). How it fits with regions,
optics and quantities: [Resources in Wiz](resources.md); the example is
`examples/resources.wiz`.

`lib/Ref.wiz` puts mutable cells in `IO` under linear points-to tokens (plan CS7b). A
location `l : Loc V` is an ordinary value. Owning the cell is a separate token `Pts l v`
at quantity 1, so one owner per cell, no leak, no double free and no use after free are
all type errors. The token's ghost index is the cell's value, so a function's type is its
Hoare triple: `swap : (1 tp : Pts p a) → (1 tq : Pts q b) → (1 k : (1 tp : Pts p b) →
(1 tq : Pts q a) → IO B) → IO B`. `Ref.get` hands back the value with an erased proof
that it is the index. The trusted part is the four natives `wiz_ref_*` (runtime/wiz.c,
over MVar cells) and their types, kept true by an invariant the API maintains; the header
of lib/Ref.wiz has the argument. Compiled code only.

## Owned handles (`lib/Handle.wiz`) ✅

`Owned h` is the obligation to release the handle `h`: a token at quantity 1 indexed by
the handle, as `MVar.Hole m` and `Lock.Guard l` are ([25d](stages/25-concurrency.md)).
The owned constructors `File.withOwned`, `Fd.withOwned` and `Process.spawnOwned` open a
fresh handle and mint its one token; nothing else can mint one. `Handle.use` passes the
token in and hands it back, and `File.releaseOwned`, `Fd.releaseOwned` and
`Child.releaseOwned` (close, close, wait) use it up. **For handles obtained through the
owned constructors**, the release happens exactly once on every path, and there is no use
after release through this API. Handles from lib/Sys.wiz's ω API (`File.open`, …) have no
token and are not covered; the handles stay ω values, so direct calls to lib/Sys.wiz on an
owned handle are not checked either. Making the handles themselves linear (direct style,
with lib/Sys.wiz and lib/Serial.wiz moved onto this module) waits for linear Σ fields
(linear-case stage 2). Trusted: two natives (`wiz_handle_own`/`wiz_handle_disown`).

## Functors and Booleans

`lib/Functor.wiz` (`import Functor`): `Functor`, `Applicative`, `<$>`, `<*>`; every `Monad`
is an `Applicative` and every `Applicative` a `Functor`; `Monad`/`Functor` instances for
`Option`, `Except E` and `List`, and `Option.map`/`bind`, `Except.map`/`bind`,
`List.flatMap` (`List.map` is `lib/Text.wiz`'s, which Functor imports). See [13d](stages/13-language.md). The Prelude itself has `if … then …
else`, short-circuiting `&&` and `||`, and `!` ([13c](stages/13-language.md)).

## 9j: text and lists (`lib/Text.wiz`) ✅

`import Text` (only `Prelude` underneath): the string and list functions a program needs,
pure (so `#eval` runs them) and linear in their input.

* **Lists**: `List.reverse`, `revApp`, `map`, `filter`, `foldl`, `foldr`, `any`, `all`,
  `find`, `isEmpty`, `head`, `take`, `drop`, `concat`.
* **Characters**: `Char.eq`, `isSpace` (ASCII), `isDigit`.
* **Strings**: `chars`, `ofChars`, `singleton`, `length`, `isEmpty`, `eq` (also `beq`),
  `lt` (by code point), `startsWith`, `endsWith`, `stripPrefix`, `stripSuffix`
  (`Option`), `contains`, `containsChar`, `take`, `drop`, `dropEnd`, `splitOn`, `join`,
  `intercalate`, `trim`, `trimLeft`, `trimRight`, `replace`, `parseNat` (`Option Nat`),
  `lookup` (in a list of pairs keyed by strings), `elem`; `Nat.repr` (decimal, pure).
  The same functions on `List Char` are `Chars.*`.

**Cost model.** A `String` is `String.mk` around a `List Char` in the kernel *and* at
runtime (`builtin string` only changes how values print). Walking a string from the
front, prefix tests, `take`/`drop` are proportional to what they walk; `String.append a b`
copies `a`, so appending in a loop from the left is quadratic (`join` and `intercalate`
build from the right); the end of a string is far (`endsWith`, `dropEnd`, `trimRight`
reverse once); and each call into C converts the list to a C string and back. Splitting
200000 characters, joining and trimming them takes 0.1 s compiled (the `text` tests).
`Std.Str` is the native alternative for indexing.

`lib/Json.wiz`, `lib/Deriving.wiz` and `lib/Hoare.wiz` import `Text` and use its
`String.eq`, `String.chars`, `String.beq`, `Nat.repr`, `List.revApp` and `List.reverse`
instead of copies of their own (two modules declaring one name are an error at import).

## Numbers: classes, integers, words ✅

(Stage doc: docs/stages/07-type-classes.md, 7e.) The Prelude's `Add`, `Sub`, `Mul`,
`Div`, `Mod`, `Neg` and `OfNat` give `+ - * / %`, prefix `-` and numerals at every
numeric type:

| type | where | numerals | operators |
|------|-------|----------|-----------|
| `Nat` | Prelude | native literals | `+ - * / %` (natural subtraction: `2 - 3 = 0`) |
| `Int` | `lib/Int.wiz` | `5`, `-5` | `+ - * / %`, prefix `-` |
| `UIntN w` (`U8` … `U64`, `USize`, `BitVec n`) | `lib/Word.wiz` | wrap around, with a warning: `(300 : U8) = 44` | `+ - * / %`, `-` (wrapping) |
| `IntN w` (`I8` … `I64`) | `lib/Word.wiz` | `-7 : I32` | `+ - * -`, signed `/ %` (truncating, as Rust) |
| `UInt64`, `Float64` | `lib/IO.wiz` | through `ofNat` | `+ - * /` (and `%` for `UInt64`) |

* **`Int`** is `ofNat n | negSucc n`, as in Lean. Arithmetic is defined by cases on the
  natively computed Nat operations, so the kernel computes on numerals
  (`rfl : (-3 : Int) * 4 + 2 = -10`) and compiled code runs Nat's natives on the
  magnitudes (an `Int` is a small object holding a number; no native signed numbers
  yet). `builtin int := Int` makes `#eval`, `#run` and compiled `main` print `-10`
  instead of `.negSucc 9` (a printing hint, not an axiom: `#print axioms` lists nothing
  for it). Division truncates (`-7 / 2 = -3`, `-7 % 2 = -1`), like `IntN` and C. Also
  `Int.natAbs`, `Int.toNat` (negatives to 0), `Int.lt`/`le`/`beq`, and lemmas
  `Int.neg_neg`, `Int.add_zero`, `Int.zero_add`, `Int.natAbs_neg`, `Int.lt_irrefl`, `Int.abs` with `Int.abs_mul`, `Int.abs_neg`. The ring laws, `int_ring!` and the order
  are in lib/IntRing.wiz and lib/IntOrder.wiz ("Arithmetic", below).
* **Words.** One set of instances at `UIntN w` serves `U8 … U64` and `BitVec n` (aliases
  are seen through). `UIntN w` and `IntN w` have the same shape but are sealed, different
  types (22k), so `-7 / 2 : I32` is signed division and `x / 2 : U32` unsigned. Their
  constructors are private to `lib/Word.wiz` and carry the proof that the bits are below
  `2^w` (22l, erased): build a word with `ofNat`, read it with `toNat`, and use
  `UIntN.toNat_lt` for the range (`UIntN.ext`: same bits, same word; `UIntN.cases1`, in
  `lib/BitVec.wiz`: a one-bit word is 0 or 1). Compiled, `a + b : U32` is the native `wiz_word_add` (the dictionary is
  inlined away), as `UIntN.add a b` was.

## Arithmetic: laws, orders and ring normalisers ✅

Moved from the dogfooding package wiz-reals (its finding G2: lib/ had no arithmetic
library, so it proved everything from `0` and `succ`). Each module has a module doc
and doc comments; std's tests check one example of each.

| module | contents |
|--------|----------|
| `lib/Order.wiz` | the classes `LE`, `LT`, `Equiv`: notation `a ≤ b`, `a < b`, `a ≈ b` (propositions) |
| `lib/Nat.wiz` | `congrArg`, `congrArg2`, `Eq.mp'`, `Eq.via`; the commutative semiring laws of `Nat`, cancellation, truncated subtraction; `Nat.Le`/`Nat.Lt` (`Nat.le m n = .true`, so many facts are `rfl`) with `≤`/`<` instances; `Ordering`, `Nat.cmp` |
| `lib/Ring.wiz` | `nat_ring! lhs = rhs`: identities of commutative semirings at `Nat`, by reflection |
| `lib/IntRing.wiz` | `int_ring! lhs = rhs` at `Int`; the ring laws `Int.add_comm` … `Int.neg_mul`; the pair representation `Int.ofPair a b = a - b` |
| `lib/IntOrder.wiz` | `Int.Le`/`Int.Lt` (`b - a` not negative) with `≤`/`<`; monotonicity, cancellation, `Int.abs` and the triangle inequality |
| `lib/Rat.wiz` | `Q`: unreduced fractions with `≈`, an ordered field up to `≈` (`Q.inv`, `Q.mul_inv`, `Q.abs_add`, `Q.lt_ceil`); `q_ring! lhs ≈ rhs` |
| `lib/RingTactic.wiz` | `by ring`: the three normalisers as a tactic that reads the goal |

```
import Rat

def t (a b c : Nat) : (a + b) * c = c * b + a * c := nat_ring! (a + b) * c = c * b + a * c
def u (a b : Int) : (a - b) * (a + b) = a * a - b * b := int_ring! (a - b) * (a + b) = a * a - b * b
def v (p q : Q) : (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q :=
  q_ring! (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q
```

* **The normalisers** read the syntax of the equation (`+`, `*`, `-`, parentheses,
  ascriptions, numerals, and `Nat.succ` at `Nat`); every other subterm is an atom,
  compared by its syntax. Each side is reified as an expression over atoms
  (`NatExpr`, `IntExpr`, `QExpr`), normalised to a sorted list of monomials, and the
  macro expands to `X.proveAt lhs rhs ρ e₁ e₂ rfl rfl rfl`: the kernel checks that the
  expressions evaluate to the sides and that their normal forms agree (with a Boolean
  comparison: an `rfl` at a list type computes through OTT's Σ of equations and is much
  slower). Soundness is proved once (`NatExpr.eval_norm`, …), so no axiom is involved.
* **`by ring`** (`lib/RingTactic.wiz`) reads the goal instead of repeating it: after
  introducing its `∀`s, a goal `lhs = rhs` at `Nat` or `Int` (seen through
  `TacticM.eqView`, stage 28b) or `lhs ≈ rhs` at `Q`. It reifies the *elaborated* sides
  (`Add.add`/`HAdd.hAdd`, `Mul.mul`, `Sub.sub`, `Neg.neg`, `Nat.add` …, `OfNat.ofNat`,
  literals, `Nat.succ`; atoms compared with `Expr.beq`, so `f x` and `f (x)` are one
  atom), compares the normal forms itself (a false identity is an error naming both
  sides) and closes the goal with `NatExpr.prove ρ e₁ e₂ Ring.trivial` (or `IntExpr`,
  `QExpr`), which the kernel checks by computing. `def t (a b : Int) : (a - b) * (a + b)
  = a * a - b * b := by ring`.
* **The `!` forms are term macros**, so the equation is written twice (statement and
  proof): a term macro sees only its own syntax. They remain for terms (`Eq.trans (…)
  (int_ring! …)`), where no goal is at hand.
* **`int_ring!` is bootstrapped.** Its soundness needs the ring laws of `Int`, proved by
  `int_pair_ring!`, which maps an integer identity through `Int.ofPair` to a `nat_ring!`
  identity (slower; use `int_ring!`).
* **`Q` is not reduced**: `p ≈ q` is `p.num · q.den = q.num · p.den`, so every law is an
  integer identity and `q_ring!` is `int_ring!` on numerators and denominators. Use the
  congruences (`Q.add_congr`, `Q.le_congr`, …) to rewrite under `≈`.
* `Vec.wiz` and `Hoare.wiz` import `Nat` for the lemmas they used to define themselves.
