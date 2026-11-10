# Stage 21: bootstrap

## 21a–c: a self-hosted backend ✅

`selfhost/Backend.wiz` compiles what the self-hosted frontend checked to C, and
`selfhost/rt.c` is its runtime. A minimal first version:

* **Erasure** (`eraseCheck`, **exercise 21.1**; `eraseInfer`), type directed through the
  self-hosted kernel (`quickType` follows elimination spines, else `infer`): types,
  proofs, sizes and quantity-`0` arguments become `◾`. A value of `μ D i` stays its
  payload, nested pairs, except for a type shaped like the natural numbers, whose
  values are native numbers (unpacked for a match). Descriptions become objects, which
  the runtime's `ind` walks to build the induction hypotheses, **lazily**: a hypothesis
  is computed when the method first reads it (eagerly, every structural function walked
  its whole argument).
* **Lazy `let`s**: the match compiler's `let`s (a shared catch-all, the hypotheses) are
  substituted when cheap (variables, projections) and else suspended with `memo`;
  evaluated eagerly they made the self-compiled compiler thousands of times slower.
* **C** (`cgE`, **exercise 21.2**): each term one C expression (GNU statement
  expressions for `let` and `case`), `λ`s lifted to C functions over their captured
  variables; a global defined by `k` `λ`s is a C function of `k` arguments, called
  directly when applied to as many (else through a curried closure); other globals are
  values built on first use. Natives by name: `Nat` arithmetic, `IO`, `Str`, arrays
  (persistent: Baker's trick), `StrMap` (a persistent treap), `memo`.
* **Runtime**: tagged words, objects collected by the Boehm garbage collector (no
  reference counts yet); the program re-executes itself once with a large stack.

**Bootstrap**: the self-hosted compiler (frontend and backend, about 6500 lines of Wiz),
compiled by the Lean toolchain, compiles itself to C (about 90 000 lines); that program
(stage 2) produces the same C as stage 1 on the inputs tried. The test suite compiles
and runs a program with the self-hosted compiler (when `$WIZ_GC_CFLAGS`/`$WIZ_GC_LDFLAGS`
point at the garbage collector).

## 21d: faster self-compilation ✅

Measured, not guessed (`perf`, per-global timestamps from a streaming driver):

* Compiling the toolchain took 5 min 43 s, almost all of it in one global: the Prelude's
  text, a string literal 2600 characters long, i.e. 2600 nested `List.cons`. Two
  quadratic costs: erasure evaluated each argument to instantiate the next parameter's
  type even when the codomain doesn't mention it (`usesVar`, as in the kernel), and the
  C text was built by appending `String`s, lists of characters (now a rope, `Doc`,
  printed piece by piece). Also `quickType` follows `scase`, `let`, `coe` and the like
  instead of inferring the whole match again at every nested split. Now 18 s.
* String literals become their code points in the C code, built once; numerals made of
  `Nat.succ`/`Nat.mul` are folded. The C went from 19 MB to 9.4 MB.
* **Multi-argument closures**: a chain of `λ`s is one C function over its captured
  variables and arguments (`mkfun`), and an application to several arguments calls it
  at once (`apn`), without the closures of the partial applications. 88 000 lifted
  functions became 35 000, the C 5.1 MB, and compiling it takes 31 s instead of 3 min.
  Stage 2 runs about twice as fast.

A note on debugging: under `gdb`, the Boehm collector's stopping of the world hangs,
because `gdb` intercepts its suspend signals; pass them through (`handle SIGPWR nostop
noprint pass`, and the same for `SIGXCPU`).

**Fixpoint.** Stage 2 (the self-hosted compiler compiled by itself) compiles the whole
toolchain to exactly the same C as stage 1 does. It took 15 minutes against stage 1's
18 s, about 70% of it the collector marking: payloads as nested pairs were about four
objects per constructor. A chain of pairs `(e₀, (e₁, … t))` is now one object, its tails
the same pointer with an offset in its low bits (taking one allocates nothing): 8½
minutes. A `match` was a method applied to the payload, a closure built and called each
time; a lambda applied to arguments is now a `let`: 6 minutes. Reference counting comes
next.

## 21g: reference counting in the self-hosted backend (first stage)

A second mode of `Backend.wiz` (`genProgramRC`), chosen by the compiler's flag `--rc`
(21k; before that, a first line `-- wiz: rc` in the program, which still works as a
fallback). The garbage-collected mode is unchanged, byte for byte.

* **Perceus on the erased terms** (`rcE`): the C is in A-normal form, one local per
  intermediate value, statements in evaluation order (C leaves the order of arguments
  unspecified, and with reference counts the order of a use and an `inc` matters).
  Liveness is one backward pass: a term is compiled knowing the variables used after it
  (by de Bruijn level), and returns those used from its start; arguments are compiled
  right to left. The last use of a variable moves it, earlier uses `inc` it, and a
  variable that dies unused is `dec`ed where it dies (after its `let`, at a function's
  start, at the start of each `case` branch that doesn't use it). A projection path from
  a variable reads in place and `inc`s only the field; a `case` on a variable's field
  reads the tag in place.
* **Runtime** (`rt.c` with `WIZ_RC`): a count in every object's header; functions own
  their arguments; function closures pass their collected arguments on (moved out when
  unique); freeing is a worklist (a list a million long frees without recursion);
  `memo` and the lazy hypotheses of `ind` release their suspension once forced; arrays
  are updated in place when unique, else copied (Baker's versions would make cycles);
  map nodes hold their keys. Constants (globals, string literals) are roots, released at
  exit, after which the program checks that every object was freed.

* **Borrowed parameters** (as in Lean): a parameter of a global function that its body
  only reads (projections, a `case`'s tag, borrowed arguments of direct calls) is
  borrowed, found as a greatest fixed point over all functions. A caller lends a
  variable to it (and releases it after the call if that was its last use); the function
  neither `inc`s it nor releases it.

* **Reuse** (Perceus' reuse tokens, as [stage 8c](08-backend.md)): in a branch of a
  `case` on an owned variable `x`, an object built after `x` dies takes `x`'s cell when
  `x` was unique and of the same size class (`reset`/`reuseobj`). Compiling backwards,
  the allocation comes first and leaves a wish for a cell; the place where `x` dies (its
  last projection, a call it was lent to, the branch's start) grants it. Tokens stay
  inside their branch. Constructors (globals that only build an object from their
  parameters) are put in place where they are applied, so that the object is visible to
  reuse; and, as in Lean's borrow inference, a parameter matched on where a branch builds
  an object is owned (its cell may be reused).
* **Drop specialisation**: a variable dying at its projection hands its reference to the
  field when it is unique (`dropTake`: the other fields are released and the cell freed,
  with no `inc`/`dec` of the field); an owned variable a `case` matches on and no branch
  uses dies at each branch's start, where the tag is known.

* **Strict `let`s**: a `let` that every path of its body evaluates (not under a `λ`)
  is evaluated where it stands instead of suspended (a thunk gains nothing when the
  value is needed anyway). Stage 2 on mid.wiz: 10.9% fewer allocations (thunks −30%,
  closures −23%), and the generated C is 17% smaller.
* **Static objects**: a constructor without fields is `(k, ◾)` every time; the runtime
  keeps one object per `k < 64` with a count that starts high (never freed, not counted
  as allocated), used for constant constructors in the generated code (also the
  globals that are one, put in place) and for the Bools, `nil` and `0`'s payload the
  natives make. Stage 2 on mid.wiz: 9.4% fewer allocations.
* **Tail calls kept** (Lean's `preserveTailCall`): a function calling itself in tail
  position with a borrowed parameter given something it would release after the call
  (a variable it owns, or a temporary) makes that parameter owned, so nothing follows
  the call (17 of 228 borrowed parameters of the toolchain).

**Bootstrap in this mode**: stage 1 compiles the toolchain (with the `-- wiz: rc` line)
to C, and that program (stage 2, reference counted) compiles it again to the same C,
freeing every object by the end.

Next: demand analysis for `let`s; then reference counting by default.

## 21i: phantom parameters in the self-hosted frontend ✅

Parity with 22e. `inductiveCmd` (`Frontend.wiz`) finds the parameters that no
constructor (nor the index type) mentions (`occurs` on the elaborated descriptions) and
gives each `p : P` a phantom domain (`phantomDom`): `D := p` for a type, `(0 x : P) ×
(x = p)` otherwise, none for a proof, a size, or a `D` that would raise the index type's
universe. The index type `Unit` becomes `(0 _ : D₁) → … → Unit`, and every index (the
descriptions' `ret`/`rec`, the type's `μ`, a match's `ind`) its value `fun _ … => tt`
(`phantomVal`); a constructor's index proof is `refl` there. Structures are inductive
types in this frontend, so they get the same. Erasure needs nothing new: in this kernel a
function into `Unit` is a proposition, so the tail is erased already. Not mirrored: an
indexed family with such a parameter (the Lean frontend pairs the index with the tail) is
rejected with an error, rather than accepted with the parameter forgotten. Tests:
`selfhostAgrees` runs the same declarations through both frontends.

## 21j: constructor parameters from the expected type, self-hosted ✅

Parity with the Lean elaborator's `checkApp`: a constructor with implicit parameters
applied in check mode (`appExpected`) first makes the implicit arguments'
metavariables and a placeholder for each explicit argument (`preArgs`), and unifies the
result type with the expected one. The arguments are then checked as before, against
types that mention the solved parameters (`Tagged.mk 3 : Tagged .true` where the field
is `Code b`); the placeholders are dropped. If that unification fails the arguments come
first, as before.

## 21k: command-line arguments; `--rc` ✅

`IO.argCount : IO Nat` and `IO.arg : Nat → IO String` (externs `wiz_io_arg_count`,
`wiz_io_arg`; the C and LLVM `main`s save `argc`/`argv` with `wiz_set_args`), and
`IO.args : IO (List String)` built from them, in `lib/IO.wiz` and in the self-hosted
Prelude (`selfhost/rt.c`'s natives read the `argv` that `rt_start` saves). The arguments
exclude the program's name; `#eval`/`#run` can't call them (they are C). With them the
self-hosted compiler takes its backend mode as a flag: `--rc`, `--rc-owned` or `--gc`
(`genProgramArgs`). The first-line pragma `-- wiz: rc` still works when no flag is
given, for one release. `scripts/fixpoint.sh --rc` runs the bootstrap in that mode.

## 21l: foreign functions and foreign types, self-hosted

Parity with [stage 9a](09-ffi.md) and 9d: the self-hosted compiler takes the same
`extern` and `foreign_type` declarations as the Lean one, and compiles them to the same
calls.

```
import IO
foreign_type FILE (finalizer := "fclose")
extern "fopen" (header := "stdio.h") fopen : String → String → IO FILE
extern "fputs" (header := "stdio.h") fputs : String → FILE → IO Nat
extern "strlen" (header := "string.h") strlen : String → Nat
```

* **Frontend** (`externCmd`, `foreignTypeCmd` in `Frontend.wiz`). To the checker an
  `extern` is an axiom, as before; it now also computes the marshalling kinds from the
  elaborated type (`ffiSig`), as `command.extern` does in `Elab/Command.lean`: `Nat`,
  `UInt64`, `Float64`, `String`, `Bool`, `Unit`, a foreign type, or a value passed as it
  is (a type variable, a Wiz data type, `Array`/`Str`/`StrMap`/`Bytes`); a parameter that
  is a type (or of quantity 0) is not passed; a result in `IO` takes and gives back the
  world. Anything else is the same error as the Lean frontend's. `foreign_type T` is an
  axiom `T : Type` with its finalizer. Both are recorded in a new field of `Globals`
  (`ffi : List Foreign`).
* **Backend** (`ffiDocs` in `Backend.wiz`). Each foreign function becomes a C function
  `d_g` of its arity (and `get_g`, its curried closure, or the constant computed once
  for arity 0) that converts its arguments, calls the C function and converts the
  result back, in both modes (`rt_drop` releases an argument under reference counting).
  The headers are `#include`d once each; without one, a prototype is written from the
  Wiz type, except for the runtime's own `wiz_…` functions (as `C.glue` does).
* **Runtime** (`rt.c`). The conversions (`rt_in_*`, `rt_out_*`), two new object kinds:
  `T_EXT`, a foreign pointer and its finalizer, and `T_RAW`, a 64-bit word (a `UInt64`
  or `Float64` whose top bit is set; smaller ones are scalars). Under reference counting
  the finalizer runs when the last reference goes, as in the Lean runtime; under the
  collector, when the pointer is collected (`GC_register_finalizer`), and the program
  collects once more at exit if there are any. A foreign pointer is lent to C for the
  call and released after it. The runtime functions `lib/IO.wiz` binds for `UInt64` and
  `Float64` (`wiz_u64_add`, `wiz_f64_show`, …) are in `rt.c` too, and the self-hosted
  Prelude declares the same `UInt64` and `Float64` operations.

**Tests** (`ffiAgrees`): the same program compiled by the Lean compiler and by the
self-hosted one (with the collector and with reference counting, which also checks that
nothing leaks) prints the same: C library functions through headers, numbers, strings
(UTF-8 both ways), `Bool`, `Unit`, `IO`, `UInt64` wrapping around, negative floats, a
`FILE` closed by its finalizer when its last reference goes (read back complete), and the
error for a type that can't be marshalled.

Not mirrored yet: `import_c` (9b: the frontend would need the preprocessed header, and a
C parser in Wiz), `glue` (9c), `implemented_by` (22d), `Bytes`, and big numbers (a `Nat`
is 63 bits in this runtime, so a C result above that is cut).
