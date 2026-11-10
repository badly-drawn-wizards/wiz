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
netlist, and `Verilog.emit` prints Verilog-2005. `examples/hdl.wiz` has a counter, a
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

## Logic, heap predicates and Hoare triples ✅

`lib/Logic.wiz` (`∧`, `∨`, `∃`, `↔`, `Not`, equality lemmas, `funext`, `propext`),
`lib/HProp.wiz` (model heaps, `emp`, `↦`, `⋆`, `−∗`, entailment and the separation-logic
laws) and `lib/Hoare.wiz` (`wp`, triples, the frame rule, verified swap and list reversal,
adequacy for an interpreter). See [stage 24](stages/24-separation-logic.md).

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
  are seen through). `UIntN w` and `IntN w` have the same shape (types are structural),
  so resolution compares the declared type names of a class's arguments and skips an
  instance for a different type: `-7 / 2 : I32` is signed division, `x / 2 : U32`
  unsigned. Compiled, `a + b : U32` is the native `wiz_word_add` (the dictionary is
  inlined away), as `UIntN.add a b` was.
