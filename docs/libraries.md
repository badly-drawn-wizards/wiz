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
  conversions. A bundle is a *value* (`S.bundle`), not an instance: structures are
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

Not done: shifts by a signal (a barrel shifter needs a `NetOp`), signed comparisons and
arithmetic shift, ASCII spellings of `≤ᵤ` …, `&&`/`||` on signals (they are `if`s whose
other branch is a `Bool`).

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

* **Refinement and case-analysis tools** (lib/Trace.wiz, from H14 T2):
  `Mealy.simulatesInv`/`simulatesInvOut` (refinement for the specification's reachable
  states: the one-step premise only from states satisfying an invariant it preserves),
  `Mealy.follows` (a run along a known path `F`: from `F 0` at `t`, every step `k < K`
  taken on the inputs that come, gives `stateAt (k + t) = F k`), `Mealy.seq` with
  `seq_stateAt`/`seq_outAt` (two machines in sequence, `Circuit.seq` on traces: the second
  runs on the first's outputs), `Nat.All P n`/`Nat.all_spec` (a table of the cases
  `P 0 … P (n-1)` gives `∀ k < n, P k`), `Bool.all`/`Bool.forall9` (a Boolean check of all
  2^9 inputs, `refl Bool.true`, holds at every input), `Bool.indP` (Bool elimination into
  `Prop`), and small Nat facts (`Nat.lt_succ_split`, `Nat.lt_to_succ`, `Nat.lt_self_succ`,
  `Nat.eq_of_beq`). In lib/Hdl/Temporal.wiz: `BitVec.eqOfNat` (two words with equal
  numbers are equal, when each evaluates to a word built from its number; `UIntN.ext`
  once the words carry their range, #145).

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

## H14 T2: the iCEstick UART, temporal properties

The first use of H14 T on a real design: the UART of wiz-icestick-uart
(`src/Icestick/Uart.wiz`: transmitter, two-flip-flop synchroniser, receiver), copied
unchanged into `examples/hdl-uart-temporal.wiz` (group `hdl`), with 4 clock cycles per
bit. Everything is kernel-checked, for **every input trace** and **every byte** (a byte
is 8 Booleans, `Bits8`; `byte d : BitVec 8` is the word), with no `sat_decide`, no
`native_refl` and no bit lemmas beyond four lemmas about the shift registers.

| claim | statement |
|---|---|
| `Tx.idleHigh` | □ (idle → line high): `TL.always (TL.imp Tx.idleA …) (Tx.obs xs) 0` |
| `Tx.frame`, `Tx.frameTL` | a byte `e` taken at cycle t (idle and start): for m < 40 the circuit's line at t+1+m is bit m/4 of the frame (start, `e`'s bits least significant first, stop), 4 cycles each; start is ignored meanwhile |
| `Tx.returns`, `Tx.accepts` | at t+41 the transmitter is idle again, and a start then begins the next frame |
| `Rx.receives`, `Rx.quiet`, `Rx.idleAfter` | idle at v (any counter, any register) and fed a well-formed frame of `e` (`Rx.WellFormed`: the transmitter's waveform up to the stop bit's middle): no report before v+38, `valid` with `byte e` at v+38, idle at v+39 |
| `Rx.badStop` | the same with a low stop bit: no report, idle at v+39 (the design returns to idle; the low line then starts the next frame) |
| `Rx.glitch` | a low pulse gone at the start bit's sample (v+2) is ignored: idle at v+3, register unchanged |
| `Loop.delivers`, `Loop.silent` (+ `Loop.refinesOut`) | transmitter → synchroniser → receiver (`loopC`, the board's loopback): a byte taken at t while the loopback is quiet (`Loop.Quiet`) is reported at t+41, nothing in between |
| `Loop.firstByte` | after reset, for every input trace whose first start is at t, the byte is reported at t+41 |

**Method.** (1) Specifications on friendly types: `Tx.spec`, `Rx.spec`, `Sy.spec`, with
control as Nats, data as Booleans, the state a one-constructor `inductive`. (2) The
refinement premise, one step for every reachable control state (`Tx.inv`, `Rx.inv`):
the circuit's step is first rewritten, by one `refl` with everything a variable, into
its *decision form* `Tx.G`/`Rx.G` (the same gates on plain tuples, with the comparisons
`left == 0`, `cnt == 3`, … as Booleans); the cases (44 for the transmitter, 38 + one
lemma for all 128 idle counter values of the receiver) are evaluations of the decision
form with the data as variables, plus four word lemmas (`Uart.shift_reg9`,
`Uart.bit0_reg9`, `Uart.frame_byte`, `Uart.shift8_byte`, each 2^9 Boolean evaluations
via `Bool.forall9`). The cases are generated by `scripts/gen-uart-temporal.py`. (3)
`Mealy.simulatesInv` gives the circuit's run as the image of the specification's, for
ever; `Mealy.seq_outAt` and the synchroniser's refinement give the loopback's. (4) The
properties are proved on the specifications: `Mealy.follows` (a run along a known path:
the 40 cycles of a frame, the 39 of a reception) and `Nat.all_spec` (case tables over
small Nats).

**Generalisation.** The proofs are for 4 cycles per bit; the board uses 104. Nothing
in them depends on the number except the case tables: with n cycles per bit the
transmitter has 11·n control states, the receiver 2 + 9·n (+ the idle lemma), a frame
10·n cycles and a reception 10·n − 2. The generator takes `N`; the specifications'
constants (3, 1 for the counter, 40/38/39 for the frames) become `n - 1`, `n/2 - 1`, …
For n = 104 that is ~1100 transmitter and ~950 receiver cases: the same proof, too slow
for the kernel today (see the findings), or a parametric proof by induction on the
counter (the counter lemmas `Rx.incs` are already per value).

**Findings (what H14 T and the kernel lacked).** Repros in
`/workspace/wiz-notes/perf-repros/`.
* *Eq at a record type with stuck sides* is η-split by conversion and each field
  re-walks the stuck computation: `stateAt m s0 xs (succ t) = (m (stateAt …) (xs t)).1` by
  `rfl` takes 107 s with the state `Nat × (Nat × Bits8)` and 1.8 s with a one-constructor
  inductive (`record-eq-eta/`; analysed by glued-eq: wishful `conv-sigma-eta-neutral`).
  Workaround: inductive specification states.
* *Case tables over expensive propositions*: `Nat.All P 128` whose entries are step
  equations (a few muxes) costs ~1.3 s per entry to check against the table (180 s
  for 128), while a table of closed facts costs ms. Workaround: the decision form with
  Boolean logic (`Rx.G2`, equal to `Rx.G` for all 32 comparison values), so the idle step
  is one lemma for every counter.
* *Circuit steps in types are expensive*: a proposition mentioning `txM (Tx.st …)`
  (bundle packing, the whole step) costs ~0.5 s per mention; hence the decision form,
  related to the circuit by a single `refl`.
* *Equations between circuit outputs*: composing `Rx.refinesOut` (circuit output = image
  of the specification's) with `Rx.receives` into one equation about the circuit's
  `Byte` output fails: with implicit arguments the elaborator computes the first
  equation's type into its Σ form ("expected ?a = ?b"), and with the middle terms given
  (`@Eq.trans`, or through `Eq.congrArg (fun o => o)`) the check goes over 2 GB (the
  record-η issue again, with the circuit's step as the stuck side). The circuit-level
  statements are therefore the refinement theorems (`Tx.refinesOut`, `Rx.refinesOut`,
  `Loop.refinesOut`) plus the specification-level properties; the transmitter's line
  (one field) composes fine (`Tx.frame`).
* Missing in the library, now in lib/Trace.wiz (see H14 T): `Mealy.simulatesInv`,
  `Mealy.follows`, `Mealy.seq`, `Nat.All`, `Bool.forall9`, `Bool.indP`; and
  `BitVec.eqOfNat` in lib/Hdl/Temporal.wiz.
* The temporal vocabulary had no *rigid (local) variables* (SVA's `(go, v = data) |=> …`):
  `Tx.frameTL` quantifies the byte outside the formula. `TL.during` reads its formula at
  absolute times, so "bit m/4 at offset m" is written as an explicit `∀ m < 40`.
* No `Nat` literal patterns (`| 0 =>`) in this branch's surface language (13q is
  separate), so frame bits and paths are written with `Nat.beq`/`Nat.lt` matches.
* Not proved: the unconditional loopback for arbitrary sequences of bytes (the joint
  invariant over transmitter, synchroniser and receiver phases; `Loop.Quiet` holds at
  every go of a well-spaced sequence, but only the first byte after reset is discharged,
  `Loop.firstByte`); "nothing is reported that was not sent" (needs reasoning backwards
  from a report).

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

## Logic, heap predicates and Hoare triples ✅

`lib/Logic.wiz` (`∧`, `∨`, `∃` with binder notation `∃ x : A, P`, `↔`, `¬`, ASCII
`/\`, `\/`, `exists`, `<->`, equality lemmas, `funext`, `propext`; [13e](stages/13-language.md)),
`lib/HProp.wiz` (model heaps, `emp`, `↦`, `⋆`, `−∗`, entailment and the separation-logic
laws), `lib/Hoare.wiz` (`wp`, triples, the frame rule, adequacy for an interpreter),
`lib/HoareTactics.wiz` (SLF-style automation: `xsimpl`, `xpull`, `xstep`, `xapp`, …) and
`lib/HoareExamples.wiz` (verified swap, list reversal, counter, list length, in-place map,
freeing a list). See [stage 24](stages/24-separation-logic.md).

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
  `Int.neg_neg`, `Int.add_zero`, `Int.zero_add`, `Int.natAbs_neg`, `Int.lt_irrefl`.
* **Words.** One set of instances at `UIntN w` serves `U8 … U64` and `BitVec n` (aliases
  are seen through). `UIntN w` and `IntN w` have the same shape but are sealed, different
  types (22k), so `-7 / 2 : I32` is signed division and `x / 2 : U32` unsigned. Their
  constructors are private to `lib/Word.wiz`: build a word with `ofNat` (or, when the
  value is known to be in range, `UIntN.ofBitsTrusted`) and read it with `toNat`. Compiled, `a + b : U32` is the native `wiz_word_add` (the dictionary is
  inlined away), as `UIntN.add a b` was.
