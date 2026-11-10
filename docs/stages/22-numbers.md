# Stage 22: numbers for hardware and systems code

Prerequisites shared by the HDL and Feral (decisions RD9, RD10/HD3).

## 22a: division, powers and bits ✅

The Prelude defines `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`, `Nat.log2` (and `Nat.testBit`, `a / b`) by structural
recursion on a fuel argument that bounds the number of steps, so the kernel can unfold
them. Each is registered with `builtin nat.<op>`: on numerals the kernel computes
natively (`def t : Nat.mod 300 256 = 44 := refl 44`), as do `#eval`, `#run`, C/LLVM
(`runtime/wiz.c`: machine words, GMP when big) and the self-hosted backend
(`selfhost/rt.c`; its Prelude has the same definitions). As in Lean, `n / 0 = 0`,
`Nat.mod n 0 = n` and `Nat.log2 0 = 0`. One table (`natNative?`, `Wiz/Core/Eval.lean`)
serves the kernel and both interpreters.

## 22b: `implemented_by` ✅

`attribute [implemented_by g] f` gives a definition `f` a different implementation in
compiled code: erasure (`compileReachable`) takes `g`'s code for `f`, while the kernel,
and so every proof, keeps `f`'s definition. `g` is a Wiz definition or an `extern`, and
must have `f`'s type up to conversion (checked at the attribute; `g` can't implement
`f` otherwise). The implementation is **trusted**, as in Lean: nothing proves it agrees
with the model, so tests compare them. `#eval` and `#run` follow the attribute, except
to an `extern` (the interpreters can't call C): there they run the model, which gives a
differential test for free. `#erase f` shows `f := g`. Foreign functions may now take
and return Wiz data types, passed as they are (marshalling kind `w`).

Not yet: a *type* with a native representation (`Vec A` as an array, R0b), and the
attribute in the self-hosted backend.

## 22c: machine integers ✅

`import Word` (`lib/Word.wiz`): `UIntN w`, a w-bit unsigned integer, and `IntN w`, w-bit
two's complement, both a number of bits below `2^w` (normalised by construction, so
arithmetic wraps around), with `ofNat`/`toNat`, wrapping `add`/`sub`/`mul`/`neg`,
`div`/`mod` (signed: `div` truncates towards zero and `rem` takes the dividend's sign,
as Rust; `x / 0 = 0` and `x % 0 = x` as Lean, where Rust panics), comparisons, bitwise
operations, shifts (`shiftLeft` by `k ≥ w` gives `0`; `IntN.shiftRight` is
arithmetic), `resize` (zero- or sign-extending, or truncating) and `toIntN`/`toUIntN`.

* **One width-indexed type** serves both clients: the HDL's `Unsigned n` needs any
  width (1, 5, 65, …) and Rust's `u32` is `U32 := UIntN 32` (also `U8 … U64`, `USize`,
  `I8 … I64`, with `U32.ofNat`, `I32.ofNeg`, …). Operations are named functions
  (`UIntN.add a b`, or `a.add b`) until the numeric classes (HD9) arrive.
* **The width is a phantom parameter** (`inductive UIntN (w : Nat) where | mk (toNat :
  Nat)`, since 22e/22h): no field mentions it, yet `UIntN 8` and `UIntN 16` are different
  types and `w` is inferred. (Before 22e it had to be an index, `mk {0 w : Nat} …`,
  leaving an erased slot in the object.)
* **Natives.** The kernel computes with the definitions, quickly on numerals (22a), and
  so do `#eval`/`#run`. Compiled code calls natives (`runtime/wiz.c`, `wiz_word_*`) by
  `implemented_by`: in a `uint64_t` up to 64 bits, GMP beyond, one function per
  operation for every width. A table of operations at widths 8 to 100 gives the same
  values in the kernel (`refl`), both interpreters, C and LLVM (`examples/words.wiz`:
  an FNV-1a hash, and facts proved by `refl` about named values; an equation whose
  sides still contain an unsolved implicit width when it is computed gets stuck, so
  state facts about definitions). A word is still an
  object holding a number (above `2^62`, a GMP number); unboxed words need the type-level
  `implemented_by` (22d).

## 22d: native representations: unboxed words ✅

`attribute [implemented_by mk get] T.mk` gives a type a **native representation** in
compiled code. `T.mk` is a constructor with one runtime field (the others erased);
`mk` has the constructor's type and `get` reads the field back. Erasure then never
builds the model's object: a constructor becomes `mk`, and `match` (and the generic
eliminators, which get the model's object back from `get`) reads the field with `get`.
The kernel and every proof keep the model. As with function-level `implemented_by`,
the natives are trusted, and the interpreters (`#eval`, `#run`) keep the model's
objects when `mk` or `get` is foreign, so the tables below compare the two.

`lib/Word.wiz` uses it for `UIntN w` and `IntN w` (and `NatObj`, a `Nat` passed to C
as the runtime number itself, possibly big). **A word is its bits**:

| bits b | representation | allocation |
|---|---|---|
| `b < 2^63` | a tagged scalar | none |
| `2^63 ≤ b < 2^64` | a raw 64-bit box (`WIZ_TAG_RAW`) | one cell |
| `b ≥ 2^64` (widths above 64) | a GMP number | as `Nat` |

* **Width-independent.** The representation depends only on b, so generic code over
  `UIntN w` (unknown `w`, any width: `BitVec n`, the HDL's `Unsigned n`) needs no width
  to build or read a word, and each value has exactly one representation (equality is
  a comparison of bits). `ofBits`/`toBits` convert from and to `Nat` (free below
  `2^62`).
* **Operations** are natives on that representation (`wiz_word_*` in `runtime/wiz.c`):
  `ofNat`/`ofNeg`, `+ - *`, `div`/`mod`/`rem`, comparisons, `land`/`lor`/`xor`/`not`,
  shifts and `testBit` (a shift or index of `2^64` or more counts as infinite),
  `resize` (zero- or sign-extending), `toIntN`/`toUIntN` (free). Up to 64 bits each is
  a few instructions on a `uint64_t`; the C backend pastes the runtime into the program,
  so `cc -O2` inlines them.
* **What is not unboxed.** A 64-bit value with the top bit set still takes a cell (the
  uniform representation has 63 bits of payload). Unboxing those too needs per-variable
  representations in the IR (raw `uint64_t` locals and parameters, boxed at polymorphic
  boundaries, as Lean's `UInt64`): the next step, once a measurement says it pays.
* **Self-hosted backend:** not yet (it runs the model; see the wishful note).

## 22e: phantom parameters ✅

```
inductive UIntN (w : Nat) where
  | mk (toNat : Nat)                     -- no field mentions `w`
def f (x : UIntN 8) : UIntN 16 := x      -- type mismatch
def width {ω w : Nat} (a : UIntN w) : Nat := w
#eval width (UIntN.mk 3 : UIntN 8)       -- 8: `w` is inferred
```

Types are structural, so a parameter that no field mentions used to be forgotten:
`UIntN 8` and `UIntN 16` were one type, `w` couldn't be inferred, and an HDL `Signal d A`
didn't keep clock domains apart. Now, for each such parameter `p : P`, the elaborator
(`phantomTail`, `Elab/Inductive.lean`) ends the type with `(0 phantom✝ : D) → Unit`
instead of `Unit`. That `Unit` is the end of the index type of an `inductive` or
`coinductive`, or of a structure's Σ. Here `D := p` if `p` is a type, and
`D := (0 x : P) × (x = p)` otherwise.

* `D` mentions `p` and is a type, not a proposition. Propositions compare by equivalence
  ([4c](04-data.md)), so `p = p` would have forgotten `p` again. Conversion now compares `p`, and
  unification solves it.
* The tail's only inhabitant is `fun _ => ()` (up to η). So it is still a singleton:
  constructors fill it in, patterns never see it, structure η and copattern index
  equations hold by `refl`, and `()` fills a structure's tail in a tuple.
* Erasure drops it (`erasable` knows the inaccessible binder name), so data, `#ir` and the
  C/LLVM code are those of the type without the parameter. Constructors, projections,
  `deriving` and `implemented_by` don't change. Nothing in the kernel changes either: it
  checks the encoding like any other declaration.
* Proof parameters get no phantom, and neither do sizes or quantities. A parameter whose
  `D` lives in a higher universe than the type also gets none, since the tail would
  raise the type's universe; it stays forgotten.
* For structures, `S 8 = S 16` computes through the Σ to `(x = 8) ↔ (x = 16)` under
  a binder `x`, so it is refutable (`Tests/Elab.lean`, group `phantom`). Equality of two
  `μ` types computes to the index equation only when their descriptions agree (so
  `UIntN 8 = UIntN 8` does), and the phantom is part of the description. So for an
  `inductive`, `UIntN 8 = UIntN 16` stays stuck: it is neither provable nor refutable,
  and a `cast` between such types gets stuck too.
* A `def` alias (`def Mut (ρ : Region) (A : Type) : Type := A`) unfolds, so its
  parameters never count. Declare a `structure` instead.

## 22f: the trusted base: witnesses and tracked registrations ✅

Two ways to prove `False` without writing `axiom` are closed.

* **Partial definitions need a witness.** `partial def f : T := …` is opaque to the
  kernel, so `f : T` is assumed. The kernel now takes it only with a term `w : T` it
  checks (`Decl.witness`, `addPartialDecl`; erased, so it may ignore a linear argument):
  `f` then proves nothing `w` doesn't. The elaborator finds the witness
  (`Elab/Witness.lean`): a variable of the type's `Π`s, `fun x => w`, a pair, `tt`,
  `Unit` for a sort, `Inhabited.default`, or a constant whose type ends in the type's
  head (a constructor, `StrMap.empty`) with its conclusion unified against the goal, so
  the indices must match: `mk : T .t` is no witness of `T .f`. The search proposes, the
  kernel decides. Otherwise write one: `partial (default := w) def f : T := …`, also
  inside `mutual`. The self-hosted kernel (`checkPartial`) and frontend (`wit`) do the
  same, and every partial definition of the self-hosted sources gets its witness found.
  Before, an elaborator check (`inhabitedTy`) looked only at the type's head, and
  `partial def bad : T .f := bad` proved `False`.
* **Registrations are trusted only in the library.** `builtin nat.add := K` makes `K`
  compute natively on numerals, which nothing checks against `K`'s definition. In
  `lib/` the registrations are reviewed (they match their definitions); anywhere else
  a registration is an axiom: recorded (`Globals.assumed`), warned about, and listed by
  `#print axioms d`, which shows every axiom `d` depends on through its type, value and
  witness (`axiom`s, foreign functions, `builtin key := name`; a numeral depends on the
  `nat` registrations). Registrations are also checked for shape (`nat.add : N → N → N`,
  each operation a definition), and numerals need `nat.zero` and `nat.succ`: `builtin
  nat := E` for an empty `E` and then `(0 : E)` used to overflow the stack (the kernel
  unfolded a numeral without a registered `nat.zero`).

## 22g: regions: borrow checking as typing ✅

```
def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa U64) (y : Shr ρb U64) : Result (Shr ρb U64) :=
  match U64.lt x.val y.val with
  | .true => .ok y
  | .false => .ok (Shr.weaken h x)                       -- without `h`: type mismatch
def bad {ρ : Region} (x : Shr ρ U64) : Result (Shr ρ U64) :=
  Shr.borrow ρ (U64.lit 5) (fun ρy hy y => .ok y)         -- E0515: type mismatch
```

`lib/Region.wiz` (`import Region`) is the lifetime layer of Feral's lowering
(`drafts/feral/`, RD12). A lifetime is an erased `ρ : Region`, and the borrow handles are
declared types, so with phantom parameters (22e) the region is part of their identity
and is inferred: `Shr ρ A` (`&'a A`), `Uniq ρ A` (`&'a mut A` passed in and handed back),
`Mut ρ A S` (a returned `&'a mut A` with its backward function to the lender `S`),
`MutOpt ρ A S`, and `Lent ρ S`, the lender while it is borrowed. Borrow checking is
typing:

* A borrow scope (`Shr.borrow`, `Uniq.borrow`, `Uniq.reborrow`, `Uniq.share`,
  `Uniq.zoom`, `Region.scope`) takes a body polymorphic in a fresh region, whose result
  type is chosen outside it (as `runST`), so no handle of the scope's region can leave
  it: returning a borrow of a local (E0515) or keeping one past its lender's scope
  (E0597) is a type mismatch.
* Inside a mutable borrow, the lender's name is rebound to a `Lent` token, which nothing
  accepts: using the lender, or borrowing it again, while the borrow lives (E0499,
  E0502) is a type mismatch.
* A reference flows to a place of a shorter region only through `Shr.weaken` (shared)
  or `Mut.weaken` (a returned `&mut`, covariant in its region), which take an
  `Outlives ρ ρ'` proof (erased). Proofs come from scopes (a scope nested in `σ` hands
  out `Outlives σ ρ`, so a borrow is shortened, never lengthened) and from a function's
  `'a : 'b` bounds (erased proof arguments); `Outlives` is opaque, so there is no other
  way to get one. A function returning one of two `&mut` arguments moves both into a
  `Mut ρb A (Uniq ρa A × Uniq ρb A)` (`Mut.ofUniq`, `Mut.mapBack`, `Mut.finish`) and
  needs `'a : 'b` for the first (`drafts/feral/lowered/12_pick.wiz`).

Scopes run their body at the enclosing region (regions are erased, so this is sound);
the separation comes from parametricity alone. `drafts/feral/rejected/` has the classic
errors, lowered, each rejected (`sh drafts/feral/check.sh`); test group `regions`.
The constructors of the handles are private to the module ([13b](13-language.md)), so
hand-written Wiz can't forge a handle either.

**Known gaps** (test group `regions`, the case marked KNOWN GAP, which checks that they
are *accepted* today; wishful: linear-case). Regions are enforced by the type checker;
*aliasing* is not. The handles are ω values, so a scope's body can use one twice
(`swap r r`: Rust's E0499), and the `Lent` token only shadows the lender's name, so a
body that names the token differently reads the lender while it is borrowed (E0502).
A handle can also leave its scope packed with its region (`B := (0 r : Region) × Shr r A`
is a closed type) and still be used. All three are rejected only because the lowering
(`drafts/feral/LOWERING.md`, L20) always rebinds the lender's name, uses each handle
once and never packs a region. Making the handles linear would
reject them in the kernel, but a linear variable can't be used inside a `match`
alternative today (`match` is built on `ind`, whose methods are scaled by ω) and
`Result`'s payload is ω, so it needs a case whose alternatives run once (R9a, a kernel
change). Linearity would still not be uniqueness: in-place updates stay with RC.

Linearity closes the escape for `Uniq` (the body has one handle and must hand it back,
so it can't also pack it) but not for `Shr`, which is a copy. The scope is already rank-2
(`(0 ρ : Region) → … → Result B`, `B` bound outside); what's missing is that `B` may
still *quantify* over regions. Two ways to forbid that: put regions in a universe a
scope's `B : Type` can't quantify over (`Region : Type 1`; that needs phantom
parameters to count for a parameter whose phantom would raise the universe, which they
don't today, 22e), or give each scope an erased `[RegionFree B]` instance, derived
structurally and with no instance for `Σ (r : Region)` or `Π (r : Region)`. Either way
the lowering only has to state each scope's result type (it does: the variables that
live on after the borrow), and with the second it also has to request the instance.

## 22h: one bit-vector family ✅

`BitVec n` (`lib/BitVec.wiz`) and `UIntN n` (`lib/Word.wiz`) are one type:

```
inductive UIntN (w : Nat) where | mk (toNat : Nat)   -- lib/Word.wiz: the model + natives
def BitVec (n : Nat) : Type := UIntN n               -- lib/BitVec.wiz: the HDL/proof names
def BitVec.add {ω n : Nat} (a b : BitVec n) : BitVec n := UIntN.add a b
def w (x : U32) : BitVec 32 := BitVec.add x (BitVec.ofNat 32 1)   -- no conversion
```

* **Design.** `UIntN` is the implementation: one model (a number below `2^w`), one set
  of natives (22c-d), one runtime representation (a word is its bits). `BitVec` is a
  view of it: a `def` alias plus the hardware vocabulary (`udiv`, `and`, `shl`, `lshr`,
  `ashr`, `slt`, `concat`, `extract`, `zeroExtend`, `signExtend`, `toVec`/`ofVec`, …),
  each defined as the `UIntN`/`IntN` operation it is (signed ones read the bits as
  `IntN n`, a free cast). The alias is enough because the width counts through
  `UIntN`'s phantom parameter (a `def` alias's own parameters never count, 22e):
  `BitVec 8` is not `U16`. The reverse (a `BitVec` structure `implemented_by` words)
  would need a second representation registration and conversions at every Feral/HDL
  boundary.
* **Proofs** see the definitions, which unfold to Word's model, so the BitVec lemmas
  are stated as before (`BitVec.add_comm` is `congrArg (UIntN.ofNat n)
  (Nat.add_comm …)`); `BitVec.add_eq : BitVec.add a b = UIntN.add a b` is `refl`.
  The literal tables (group `vec`) and the 34-operation and 64-bit word tables (group
  `word`) agree in the kernel, `#eval`, `#run`, C and LLVM.
* **Compiled**, a bit vector is a native word: no constructor or projection in the IR
  (group `vec`), no allocation below `2^63`. The model's object is now `⟨0 bits⟩`
  (the width no longer takes a slot), so a word read back prints as `.mk 18446744073709551613`.
* **For the HDL**: `Unsigned n`/`Signed n` (hdl-plan §2.2) can reuse the same
  representation as aliases (`def Unsigned (n : Nat) := UIntN n`, `Signed n := IntN n`);
  a `structure` wrapper would instead need its own `implemented_by mk get` to avoid a box.
  (Since 22i a one-field `structure` is unboxed anyway.)

## 22i: unboxed newtypes and `attribute [inline]` ✅

```
structure Uniq (ρ : Region) (A : Type) where
  val : A                                  -- at run time, a Uniq ρ A is its A
attribute [inline] Uniq.borrow             -- compiled code runs the scope's body in place
def push (xs : List Nat) := Uniq.borrow Region.static xs (fun ρ h v r => push1 r)
#ir push                                   -- no pap, no ap, no handle allocated
```

The region discipline of 22g used to cost at run time: every handle was a cell
(`⟨val, ◾⟩`) and every scope a closure called through `ap`. Both are gone:

* **The last field of a structure is unboxed.** A structure with fields now ends in
  its phantom tail (22e) followed by a **marker**, `(0 fields✝ : Enum [fields✝]) → Unit`,
  instead of `Unit`: `structure W where val : A` is `(val : A) × ((0 fields✝ : Enum [fields✝]) → Unit)`.
  Like a phantom tail it has one inhabitant (`fun _ => ()`, filled in by constructors and
  by `()` in a tuple), so η, `refl` and structure equality are as before. Erasure
  (`unboxedSigma`) represents a Σ whose second component ends in the marker by its first
  component: `S.mk a` is `a`, `.1` is the identity, `.2` is `◾`, and `#eval`/`#run`/
  `wiz run` read the value back the same way. So a one-field structure (a newtype:
  `Shr`, `Uniq`, `Lent`, `Mut`) is its field, and an `n`-field structure is `n − 1` pairs
  instead of `n`.
* **Why in the type.** A representation must be a function of the type *up to
  conversion*: a value converted (or cast) from one type to an equal one keeps its bits.
  A raw `A × Unit` (or a name the kernel ignores) can't carry it, since a type variable
  can stand for `Unit` and `S` converts to its Σ. The marker's domain is compared by
  conversion and its label is inaccessible, so every type convertible to a structure has
  it and no other type does; substitution can neither make nor remove it, so generic code
  and code at a known type agree. Zero-field structures and index types have no marker.
  Phantom parameters still don't change the representation (group `phantom`).
* **`attribute [inline] f`** (`Inline.lean`) substitutes `f`'s erased body where `f` is
  applied to all its arguments, then simplifies: a redex `(λ x. b) a` becomes a `let`,
  and a `let` of a variable, of `◾`, or of a lambda used once (not under a lambda) is
  substituted, so a lambda argument lands in the head of an application and is reduced.
  `lib/Region.wiz` marks its scopes and `Uniq.set`/`Shr.weaken`. The kernel never sees
  the attribute; inlining a recursive definition stops after a few levels.

Objects allocated on `#run`'s checked heap (`tests --allocs FILE ENTRY…`, a measuring
mode of the test driver), before → after:

| program (`drafts/feral/lowered`) | before | unboxed | + inline |
|---|---|---|---|
| 01 `main` (swap two `U64`s) | 12 | 6 | 4 |
| 01 `swapLists` | 11 | 7 | 5 |
| 02 `fill 5` | 106 | 82 | 32 |
| 02 `fill 50` | 5506 | 5302 | 302 |
| 07 `record` | 31 | 13 | 9 |
| 07 `record_optic` | 47 | 30 | 26 |

(`fill` was quadratic: `Uniq.set` was a call, so the vector inside the handle was
shared and `push` copied it; inlined, it is updated in place.) Not yet: case of a known
constructor, so the `.ok (q.2, q.1)` re-wrapping around each scope is still rebuilt (in
the same cells, by reuse); a recursive call through a scope's lambda is still not seen
as structural (`05_bst` `insert` stays `partial`; wishful: reborrow-recursion has a
design). The self-hosted toolchain doesn't have phantom tails at all yet.

## 22j: Feral, the surface language ✅

```
import FeralCore
import Feral
feral
  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {
    let t := *x;
    *x := *y;
    *y := t
  }
  fn main () : U64 × U64 := {
    let mut a : U64 := 1;
    let mut b : U64 := 2;
    swap (&mut a) (&mut b);
    (a, b)
  }
end
#eval Result.map (fun (p : U64 × U64) => (p.1.val, p.2.val)) main     -- .ok (2, 1)
```

**Feral** is the Rust-like language of the plan (it was "the Rust DSL"; its syntax is
Wiz's, its semantics Rust's). Until now it was a design, with programs lowered by hand
(22g). `lib/Feral.wiz` makes the surface real for the fragment the lowering rules cover:
functions with lifetime parameters and `'a : 'b` bounds, `let`/`let mut`, `&`/`&mut`
borrows and reborrows, structs and enums, `match`/`if let`, calls and library methods,
loops, `?`, `U64`, and functions that return borrows.

* **A command macro written in Wiz.** `feral … end` is ordinary `syntax` (categories
  `feral_item`, `feral_expr`, `feral_ty`, …) with a `CommandMacro` (7c) that runs in the
  interpreter: it checks the items and lowers each to Wiz **source text**, which is parsed
  and elaborated like anything else. `#lower feral … end` also shows that text: the
  function above becomes

  ```
  def swap {ρa ρb : Region} (x : (Uniq ρa U64)) (y : (Uniq ρb U64)) : Result (Unit × ((Uniq ρa U64) × (Uniq ρb U64))) :=
    let t := x.val;
    let x := (Uniq.set x y.val);
    let y := (Uniq.set y t);
    Result.ok ((), (x, y))
  ```
  and `main` is two nested `Uniq.borrow` scopes around the call. The rules are
  `drafts/feral/LOWERING.md` (L1–L23), cited in the code.
* **The checker's types carry regions.** The lowering is type-directed (`*x` is `x.val`
  on an argument borrow and `Mut.get` on a returned one), so the front end infers types,
  with regions as part of them, exactly as lib/Region.wiz has them: a borrow opens a
  scope with a fresh region, the lender becomes a `Lent` token inside, and what leaves
  the scope may not mention the region. A scope lasts from the borrow to the last
  statement that mentions something tied to its region.
* **Borrow errors, twice.** The front end reports E0499, E0502, E0506, E0515, E0597 and
  "lifetime may not live long enough" at the Feral expression. They are also type errors
  of the lowered program: `#unchecked feral … end` lowers without the front end's
  verdict, and the kernel rejects the result. The tests run every rejected program both
  ways, so the two can't drift apart.
* **What Feral is and isn't.** A Feral program *is* the Wiz program `#lower` shows;
  soundness never depends on the front end. But aliasing — one live `&mut`, no use of a
  lender while it is lent — is enforced by the **shape** of the lowering (scopes that
  rebind the lender's name, handles never emitted twice), not by linearity: handles are
  ω values (22g, known gaps). One Feral program shows it: `swap (&mut a) (&mut a)` is
  E0499 in the front end, yet its `#unchecked` lowering checks. The surface language
  never names handles, scopes or tokens, so when handles become linear only the text
  emitted for scopes changes.
* **Located output for command macros.** Runtime `Syntax` has no positions. A command
  macro now names a node of its input by **path** (child indices), and its output may
  contain `Syntax.errorAt path msg`, `Syntax.infoAt path msg` and
  `Syntax.sourceAt path text` (`Elab/ProcMacro.lean`, `pathInfo`): diagnostics at that
  node, and Wiz source parsed as commands and positioned there. Generated source that
  fails to check is reported at the node with its text.

Limitations: the fragment (LOWERING.md §1a); spec clauses are not parsed; `U64` and `Vec`
are the stand-ins of `drafts/feral/lib/FeralCore.wiz`; keywords such as `if` and `mut`
are reserved in a file that imports `Feral`; errors inside generated code point at the
whole item; one borrow error per function; stricter than rustc where a `&mut` would be
implicitly reborrowed at a shorter lifetime.
