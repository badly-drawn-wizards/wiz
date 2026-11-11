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
* **Demand analysis for `let`s** (replacing "used on every path"): a source `let` is
  only marked during erasure and decided after pushing and inlining, by a backwards
  analysis (`dmdA`) of how its body uses the variable: bottom (every path ends in
  `unreachable`), strict (evaluated on every path), lazy (on some), or absent, with a
  use count. Strict `let`s are evaluated where they stand, absent ones dropped, and a
  `let` that only one branch of a `case` uses (not its scrutinee) moves into that branch
  and is decided again there; the rest are suspended as before. Application is call by
  value, so only a suspended value and a `λ`'s body are lazy. Stage 2 compiling the
  toolchain: thunks −68%, allocations −10%, peak live objects −8%, C 6% smaller.
  (Absent parameters, found as a fixed point over signatures and passed `◾`, were tried
  and dropped: the analysis cost as much as it saved.)
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

* **Small branching functions inlined with suspended arguments**: a global whose body
  is a `case` on a parameter with cheap branches (`Bool.and`, `Bool.or`, …) is put in
  place at saturated calls with its arguments bound by marked `let`s, so the demand
  analysis evaluates an argument only in the branches that use it: `Bool.and a b` no
  longer evaluates `b` when `a` is false (call by value did, and `conv`, `tmEq`, `occurs`
  and the like recursed through it).
* **Unmemoised hypotheses** (`indv`): when the method of an `ind` reads its hypotheses
  only as hypotheses (`hs.1ʲ.0`), each at most once on every path and not under a `λ`,
  or is itself a `λ` (a function-valued motive), it gets a view of the payload instead
  of the chain of suspensions, and a read computes the hypothesis where it stands
  (`p_hypAt`). Any other use of `hs` keeps the memoised chain.
* **Static constants**: a `λ` capturing nothing and an object built only from constants
  (an `ind`'s description, typically) are built once, kept as roots and released at
  exit (before the leak check, as string literals).

  Stage 2 compiling the toolchain, same input: 5232 M allocations with master's backend,
  2200 M with these three (−58%); peak live objects +11% (the constants), C +16%.

Next: reference counting by default.

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

## 21m: written quantities in the self-hosted frontend

Finding K10 of audit 2: `Frontend.wiz` built every binder at ω, whatever was written, so
`def twice (1 x : Nat) (f : Nat → Nat → Nat) : Nat := f x x` was accepted. It now reads
the binder's `quantity` node as `elabQuantity` does in the Lean elaborator (`binderQ`,
`writtenQ`): `0`, `1` or `ω`, by default ω on an explicit binder and 0 on an implicit
one; a numeral other than 0 or 1, or a quantity term `%t`, is an error. The quantities
reach the kernel, which already checks usage (`popUsage`):

* the binders of a `def`, an `axiom` and a partial definition's signature (`defT`,
  `teleT`, and the match-compiled definitions' telescope, `piTeleQ`), `(1 x : A) → B`
  (`depPis`, and `pis` in the scope checker for constructor field types), and a typed
  `fun` (`inferLams`);
* a `fun` checked against a Π: a written quantity must be the Π's ("binder quantity 1
  does not match the expected ω", as `checkFun`); an unwritten one takes it;
* `let 1 x := v; b` is the kernel's `letq` (the backend erases the value of a `let 0`);
* a constructor's parameters are implicit at 0 (the Lean elaborator's `implicitΔ`), so
  `List.cons` is `(x0 :0 U0) → (x1 : x0) → …`; an inductive type's own parameters keep
  their binders' quantities. The helper definition that `withDefault'` makes writes an
  implicit binder's 0 out when it makes the binder explicit.

Erasure needs nothing new: arguments at 0 were erased already, and there are more of
them now (an implicit `{w : Nat}` is no longer passed). The self-hosted sources needed no
change: the Lean frontend checks them with the same rules.

What does not match the Lean frontend (pinned in a test, and in
[CoreSpec §15](../CoreSpec.md)): a linear variable used once in each branch of a `match`
is accepted here (the kernel's case joins the branches' usage) and rejected there (a
branch is an ω argument of `T.casesOn`); a constructor field with a quantity is an error
here, since `Kernel.wiz`'s descriptions have none; implicit constructor fields don't
exist here. An unused linear variable (`def drop (1 x : Nat) : Nat := Nat.zero`) and a
match on a linear variable are rejected by both, through the kernel's `popUsage` and
eliminator rules (PR #84).

**Tests** (group `selfhost`): `selfhostAgrees` runs 23 declarations through both
frontends (accepted and rejected alike: linear functions passed and used twice, `let 1`,
`let 0`, implicit parameters used at runtime, a `fun`'s quantity against the expected
one, a quantity `2`); `selfhostVerdicts` pins the three differences above; a program
with quantities is compiled and run under both collectors.

## 21n: `private`, and unknown commands, in the self-hosted frontend

Parity with [13b](13-language.md) as far as it is reachable. `private def …` (any
`command.private`: a definition, axiom, partial definition, `mutual` block, inductive
type or structure) was an error here ("unsupported syntax command.def"); private
constructors (`| private c`), private fields and `private mk ::` were parsed and ignored.
Now `private` before a command declares the same names as without it.

**Privacy is not enforced, because nothing can reach it.** In the Lean toolchain a private
name is private to its *module*: another module gets "'x' is private to module M", and
there a type with private parts is opaque (it equals only itself, isn't matched, isn't
built by tuples or look-alike types; its recursors are private). The module itself sees
everything as usual. The self-hosted toolchain has exactly one module, the input file:
every `import` loads the frontend's own Prelude (`preludeText`), which declares nothing
private. So every check of 13b is about a use from another module, and in a one-module
world each of them holds vacuously; treating `private` as public there is exactly the
Lean frontend's behaviour inside the declaring module. Mirrored: the syntax in every
position, and the in-module meaning. Not mirrored, and unreachable: the "private to
module" errors, the opacity of types with private constructors or fields outside the
module, private recursors. PR #79's `T.desc` and `--strict-privacy` are the same (module
crossing). **The day the self-hosted toolchain gets modules**, privacy must come with them:
`Globals` needs each name's module (and whether it is private); `Scope.lookup` from
another module must reject a private name; a type with a private constructor or field
must become an opaque constant outside its module (no unfolding of its `μ` in the
frontend's conversion, no `match`, `.1` or constructor through the Σ), while the kernel
keeps checking against the full definition, as 13b's elaborator view does.

An unknown command, or a modifier the frontend doesn't know (`sealed`, `noncomputable`
when the grammar gets them), is an error naming it ("unsupported command
command.sealed"), never ignored.

## 21o: `link_c`, `link_lib` and `export`, self-hosted

Parity with [9f](09-ffi.md) and the first half of 9g.

* **`link_c "f.c"`, `link_lib "m"`** (`linkCmd` in `Frontend.wiz`): recorded once each in
  `Globals`' foreign declarations (a new constructor `Foreign.link`), with the Lean
  frontend's check of a library name. The self-hosted compiler prints one C file with the
  runtime included, so it can't link anything itself: it names the files and libraries
  in the first lines of its output, `// wiz-link-c: f.c` and `// wiz-link-lib: m`, and
  whoever compiles that C adds them (`cc out.c f.c -lm`; the tests do). A path is the one
  written, relative to the input file's directory; the frontend is pure, so a missing
  file is reported by the C compiler rather than at the `link_c`.
* **`export "c_name" f (: T)?`** (`exportCmd`; `Foreign.exported`): the same checks and
  messages as `command.export` (the declaration exists, the optional type converts with
  its type, a C identifier, not exported twice, arguments `Nat`, `UInt64`, `Float64`,
  `String`, `Bool`, a foreign pointer or a Wiz value, a result among those but not a
  foreign pointer, or `Unit`, maybe in `IO`). The backend (`exportDocs`) writes a C
  function `c_name` after the program's definitions, in both modes: C values become Wiz
  values (a `String` copied, a foreign pointer lent without a finalizer, a `Bool` from
  `int`), the definition's closure is applied (`get_f`, with the world for `IO`, whose
  result is the pair's first field), and the result is converted back (a `String` as a
  `malloc`ed `char *` the caller frees, `rt_export_str`; `Unit` as `void`).

Not mirrored: callbacks (a parameter of function type, `Callback`), `c_struct` (9i),
`--lib`/`--no-main` builds and the `.h` file of the exports, and the handle functions
`wiz_retain`/`wiz_release`/`wiz_live_objects` (a Wiz value given to C is a plain word
here; under reference counting C owns the reference it gets, as in 9g, but can't make or
drop one). An exported function is called while the Wiz program runs (from C code it
called), as in the test; the runtime isn't set up for a C `main` of its own.

## 21p: a C `Nat` that doesn't fit is an error

A `Nat` in the self-hosted runtime is a 63-bit scalar (PR #80 makes a numeral from 2^63 on
an error). A foreign function's `Nat` result, or a `Nat` argument C passes to an export,
from 2^63 on used to be cut silently; `rt_out_nat` now stops the program with "a
foreign function's Nat does not fit in 63 bits" (exit code 3). The Lean toolchain's
`Nat`s are unbounded, so there the same program prints the number: a known difference.
UInt64 is unaffected (its large values are objects).

**Tests** (group `selfhost`): `private` in every position both frontends take it, and
`private` inside `mutual` rejected by both; unknown commands named in the error; the
`export`/`link_lib` checks (9 declarations, same verdicts); one program with exports
(numbers, strings both ways, `Bool`, `IO`) called from a `link_c` file and `link_lib
"m"`, run by the Lean compiler and by the self-hosted one in both modes, same output;
the 63-bit error in both modes against the Lean toolchain's answer.

## 21u: Σ types, `∀`, `#eval` and `attribute [inline]` in the self-hosted frontend

`Frontend.wiz` elaborates the rest of the Lean frontend's Σ and Π syntax (`inferT2`,
`checkTuple`): `A × B` (`term.prod`), `(x : A) × B` with a written quantity
(`term.depSigma`, `depSigmas`), `(a, b, …)` (`term.tuple`: checked against a Σ type, or
inferred as `A × (B × …)` and annotated, since the kernel can't infer a pair), `.1`/`.2`
(`term.proj`), and `∀ x (y : A) {z : B}, C` (`term.forall`; a binder without a type gets a
hole, a metavariable in `Type`). A hole `_` in a type position is now a metavariable too.
There is still no `let (x, y) := …` (`Kernel.wiz` has no `split`, §7.1 of CoreSpec).

`#eval t` is `#reduce t` (the value is printed as the kernel's normal form, not as the
Lean toolchain prints it), and `attribute [inline] f` is checked as in the Lean frontend
(`f` must be a declaration with a definition) and otherwise ignored: inlining is a hint
to the Lean compiler. Not checked here: a second `attribute [inline]` of the same name
(an error in the Lean frontend).

**Tests** (group `selfhost`): 10 Σ/∀ declarations with the same verdicts in both
frontends; `#eval` and `attribute [inline]` (5 verdicts and one output).

## 21v: a linear variable in every branch of a `match` (`T.casesOnA`)

Until now the Lean frontend rejected `def m1 (1 x : Nat) (b : Bool) : Nat := match b with
| .true => x | .false => x` and the self-hosted one accepted it (21m). The self-hosted
frontend was right: `x` is used once on every path, and the kernel's `ecase` joins its
branches' usage (CoreSpec §5.3, `1 ⊔ 1 = 1`). The Lean elaborator compiled the match to
`Bool.casesOn motive m_true m_false b`, whose methods are separate ω arguments, so the
two uses added up to ω.

Every inductive type now also gets `T.casesOnA` (E1 of
/workspace/wiz-notes/linear-case-design.md; `mkRecursor … (additive := true)`): the
methods are bundled into one argument at quantity 1, a function from the tag,

    T.casesOnA : {Δ} → (motive : …) → (1 m : (t : Enum ls) → ecase t [ULift M_c, …]) →
                 {ξ} → (x : T Δ ξ) → motive ξ x

where `M_c` is `T.casesOn`'s method type for `c`, lifted to `Sort (imax (l+1) v)` so that
all branches of the type-level `ecase` live in one universe (universes aren't cumulative).
Its body is the sized case `scase` at `∞` (which runs its method once and doesn't scale it)
calling `down (m 'c)` on the fields. A `match` with a variable bound at a literal
quantity other than 0 and ω in scope (`LocalCtx.linearLvls`: `def`/`fun` binders, `let
1`, equation parameters) passes `fun t => ecase t [up m_c, …]` instead of the separate
methods; a reverted column that is linear is re-bound at 1. Everything else elaborates
exactly as before, to `casesOn`. Structural recursion (`T.rec`) and sized matches are not
additive: a linear variable used by a recursive call is used once per node.

**No kernel change**: `T.casesOnA` and every term using it are checked by the kernel like
all declarations (the usage checker is not on the path changed here; its rules for
`ecase`, `scase`, `up`/`down` were already there). The compiler has no special case for
`casesOnA` (Erase.lean unfolds `casesOn` calls by name), so such a match compiles through
the generic path: correct, possibly slower; only matches with a linear variable in scope
take it.

**Tests** (group `selfhost`): 12 declarations, both frontends alike (Bool, Nat, Option,
List, an indexed family, nested matches, `let 1`; dropping the variable in one branch, or
using it twice or under an ω argument, rejected); a compiled program with additive matches.
