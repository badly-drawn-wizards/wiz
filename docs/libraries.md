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
def top : Circuit In.code Out.code := Circuit.bundled Tx.bundle In.bundle Out.bundle init (BStep.mk …)
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
  instance resolution could not tell their bundles apart.
* **Composition** (Lava/Clash-style arrows): `Circuit.comb`, `delay`, `seq`, `par`,
  `loop` (feedback through a register), `named` (names the state), `mapIn`/`mapOut`,
  `inputName`/`outputName`, and `Circuit.inst c s x` for an instance with its own state
  inside a hand-written step. Each has its semantics as a lemma: `Circuit.runFrom_seq`,
  `run_seq` (`run (seq a b) xs = run b (run a xs)`), `run_par`, `run_delay`,
  `runFrom_loop`, `run_named`, `runFrom_comb`, `inst_el`, `stepEl_withReset`/`Enable`.
  Combinational code passed to a combinator is a `Comb i o` value (a polymorphic
  function cannot be applied under a step's own representation binder; see the
  wishful notes on non-linear unification spines). The netlist is flat.
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

Not done: module hierarchy in the Verilog, enumerations at `HwTy`, numerals and operators
at `r (bits n)` (instances of the numeric classes, when they land: `Add`, `Sub`, `Mul`,
`Neg`, `OfNat` at `r (HwTy.bits n)` through `Hw`), wire names from `let` binders (an
elaborator hook, wishful `hdl-let-names`), asynchronous reset, several clocks.

## Logic, heap predicates and Hoare triples ✅

`lib/Logic.wiz` (`∧`, `∨`, `∃`, `↔`, `Not`, equality lemmas, `funext`, `propext`),
`lib/HProp.wiz` (model heaps, `emp`, `↦`, `⋆`, `−∗`, entailment and the separation-logic
laws), `lib/Hoare.wiz` (`wp`, triples, the frame rule, adequacy for an interpreter),
`lib/HoareTactics.wiz` (SLF-style automation: `xsimpl`, `xpull`, `xstep`, `xapp`, …) and
`lib/HoareExamples.wiz` (verified swap, list reversal, counter, list length, in-place map,
freeing a list). See [stage 24](stages/24-separation-logic.md).
