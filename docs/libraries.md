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

## Logic, heap predicates and Hoare triples ✅

`lib/Logic.wiz` (`∧`, `∨`, `∃`, `↔`, `Not`, equality lemmas, `funext`, `propext`),
`lib/HProp.wiz` (model heaps, `emp`, `↦`, `⋆`, `−∗`, entailment and the separation-logic
laws) and `lib/Hoare.wiz` (`wp`, triples, the frame rule, verified swap and list reversal,
adequacy for an interpreter). See [stage 24](stages/24-separation-logic.md).

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

Not yet unified: `lib/Json.wiz` (`String.eq`, `String.chars`, `Nat.repr`),
`lib/Deriving.wiz` (`Nat.repr`, `String.beq`), `lib/Hoare.wiz` (`List.revApp`,
`List.reverse`) and `lib/Hdl/Core.wiz` (`List.map`) define some of the same names. The
definitions agree, and when two imported modules define a name the later import's wins
silently, so importing them together works today; the fix is for each of them to import
`Text` and drop its copy.
