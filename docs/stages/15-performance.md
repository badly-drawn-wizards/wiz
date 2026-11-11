# Stage 15: performance for self-hosting

## 15a: lazy unfolding ✅

`memo : (Unit → A) → Unit → A` (Prelude, `builtin memo`) is a memoised suspension. To
the kernel and the interpreters it is the identity; compiled code makes it a thunk
object (`WIZ_TAG_THUNK`) that `wiz_apply` runs at most once, keeping the result. The
Wiz kernel's glued values now hold their unfolding as `Unit → Val` built with `memo`, as
the Lean kernel's `Val.unfold` holds a `Thunk`: a global is unfolded only when `whnf`
looks through it, and once. Checking a term that mentions a large global 300 times
(without needing its value) went from 206 s to 1 s.

(`whnf` recurses into the forced unfolding: structural recursion through a function
field. For a mutual family, that field's induction hypothesis wants the index equation
after the field's argument; the recursive call now supplies it, as `fun h => ih h
proof`.)

## 15b: the self-hosted pipeline, measured ✅

A benchmark checks a file of 300 definitions (and one of 3000) with the self-hosted
pipeline compiled to C, against the Lean-hosted `wiz check`. At first the self-hosted
one took 1.5 s (and 32 s, so quadratic) against 0.08 s (0.68 s). Profiling the compiled
program with `gprof` (`WIZ_CFLAGS=-pg`):

* the parser spent nearly all its time reading tokens, each read trying every token of
  the table: the context now keeps the table by first character (`tokenBuckets`), and
  a candidate no longer shares the memo table with the live state;
* globals were variables of the typing context, so every command rebuilt it, and every
  usage vector and name lookup grew with the number of globals: they are now the
  kernel's constants (checked in the empty context, unfolded lazily since 15a), found
  by name in a `StrMap` (`Scope`), and kept in an `Array`.

Now 0.25 s (2.4 s): linear, within 3–4× of the Lean-hosted checker. The profile is flat;
the largest share left is reference counting (about 1.4 billion `inc`/`dec` for the
3000 definitions). Two things tried and left out:

* *borrow inference* as a pass around `insertRC` (parameters never consumed are
  borrowed; calls and boxed wrappers fixed up afterwards) removed only 4% of the
  `inc`s, and cost 12% more allocations, since a borrowed cell can't be reused. The
  gain needs borrowed *projections* and reuse-aware inference inside `insertRC`
  itself;
* `ap` of a known partial application: closures are applied only about a million
  times here.

Next: fewer index equations for mutual families (elaboration time and code size).

### 15c: known constructors and constant folding ✅

`Wiz/Compiler/Simp.lean` simplifies every function of the IR right after lowering
(before constants are hoisted and before reference counting). A native operation on
numbers whose arguments are literals is computed at compile time, with the kernel's own
semantics (`natNative?`: `3 - 5 = 0`, `n / 0 = 0`, `n % 0 = n`); `nat.beq`/`nat.blt` of
literals, or of a variable with itself, are the `Bool` tags. A `case` on a variable known
to be a constructor (built in the same function), a literal, or already tested by an
enclosing `case` is replaced by the branch, and a projection of a known constructor is
its field. A branch also learns from its test: in the `true` branch of
`case (nat.beq n 10)`, `n` is `10`. What becomes unused is removed by `elimDead`, which
now counts operations on numbers, tests and tags as pure. `#ir` shows the folded form;
`#run`, C and LLVM agree (group `c`/`llvm`: "constant folding and known constructors").

### 15d: the self-hosted C at `-O2` ✅

Stage 2 of the bootstrap (`scripts/fixpoint.sh`, grail's `stage2` target) and the
self-hosted compile-and-run tests compile the self-hosted backend's C with `-O2`
instead of `-O1`, like `wiz build`.

### 15e: dead code in the self-hosted backend ✅

The reference counting mode compiles a `let`'s body first, so it knows whether the
variable is live: a dead `let` whose value has no effects (variables, globals, numbers,
objects and projections of such, closures, suspensions; no applications) is not
compiled at all. Before, it was computed and released at once.

### 15f: self tail calls are loops ✅

A function that calls itself in tail position runs in constant stack, whatever the C
compiler does (tested at `-O0` on a 1 MB stack, 10 million iterations). In the Lean
compiler (`Decl.loopify`), `f ps` whose body has `let r := f as; ret r` (in a branch, a
join point's body, …) becomes `join J(ps') := body[ps ↦ ps', f as ↦ jmp J as]; jmp J ps`; join
points are labels and `goto`s in C and branches in LLVM, and borrow inference (8e)
treats the join point's parameters like the function's. In the self-hosted backend (`markSelf`),
such a call becomes `wiz.self`: the arguments are computed, the parameters reassigned
and control goes back to the label `top_` at the function's start (in the garbage
collected mode, out of the statement expressions; that mode now pushes applications
into `case`s too, as reference counting did, so a match builds no closure and the calls
in its branches are in tail position). Under reference counting a borrowed
parameter must be passed a borrowed parameter (else the argument would be released
after the call): otherwise the call stays a call. In the garbage collected mode a call
under a match on a computed value (`match Nat.beq … with`) is not yet in tail position:
the match's payload is a suspended `let`, and its branches are closures (under reference
counting lets are strict, and it is a loop).

### 15g: big numerals ✅

A numeral like `1000000000` in a file compiled by the self-hosted compiler crashed the
compiler (a stack overflow), when that compiler was the one built by the Lean
`wiz build`. The self-hosted kernel has no number literals: its frontend elaborates a
numeral to a binary term, `2 * (n / 2)` plus one if `n` is odd (`binNat`), and it
halved `n` with `halfNat`, a recursion on `succ (succ j)`: `n / 2` frames deep. It now
uses `Nat.div`, a native operation in both compilers; the term was always logarithmic.

What each compiler does with a numeral:

* **The Lean compiler** keeps it as a literal from the elaborator to the IR
  (`Term.natLit`, `ETerm.natLit`, `Expr.lit`), and the backends emit a constant: below
  `2^62` an immediate, from `2^62` a GMP number built once from its digits
  (`wiz_nat_lit`). Nothing recurses on the value. One bug on the way: the LLVM backend
  named the global holding the digits with a counter per function, so a module with
  two such literals in two functions defined `@lit.1.str` twice and `llc` rejected it;
  the global is now named after the number.
* **The self-hosted compiler.** Its numbers are 63-bit words whose arithmetic wraps
  (a limit of that runtime, not changed here), so a numeral from `2^63` could only be
  its value modulo `2^63` (`2^64 + 1` would be `1`). It is now an error in the frontend
  ("the numeral does not fit in 63 bits"), decided on the digits: when the compiler
  runs on words itself, the value has wrapped before anyone can look at it.
* **The self-hosted compiler stops at a frontend error.** Its driver
  (`Selfhost.compilerSource`) printed the frontend's messages as comments at the top
  of the C and went on: a definition with an error was just missing, and the program
  compiled anyway if nothing used it. Now, if any line of the frontend's output starts
  with `error`, the errors go to standard error, no C is printed, and the exit code is
  1. For this the self-hosted prelude and `selfhost/rt.c` have two more natives, with
  the names and types of `lib/Sys.wiz`: `IO.ePrintln : String → IO Unit` and
  `Process.exit : Nat → IO Unit`.
* **Folded constants.** The backend recognises the binary term and emits `BOX(n)` (`natConst`, which also
  folds `+` and `*` of constants): it now wraps like the runtime does. Built by the Lean
  compiler its own numbers are unbounded, and a folded product could print a constant
  like `BOX(18446744073709551616UL)`, which gcc truncates with a warning and other C
  compilers reject (and stage 1 and stage 2 would print different C).

Tests: numerals at `2^31`, `2^32`, `2^62 - 1`, `2^62`, `2^63`, `2^64`, `2^64 + 1` and
`10^30` with `#eval`, `#run`, C and LLVM (groups `backend`, `c`, `llvm`); with the
self-hosted compiler (group `selfhost`), numerals up to `2^63 - 1` compiled and run
with both collectors, the error from `2^63`, and the compiler's exit code and
standard error for a program with errors.

### 15h: case-shaped calls (`Bool.and` and `Bool.or` short-circuit) ✅

Application is call by value in compiled code: `Bool.and a b` computed `b` before
looking at `a`. So `p x && all p xs` (written with `Bool.and`) walked the whole list
after the answer was known, and the recursive call was not a tail call. The kernel's
evaluator never did that (it is lazy).

A definition is **case-shaped** when its erased code is `λ x₁ … xₙ. case s [b₀, …]`
with a scrutinee and branches built only from the parameters, constants, objects,
projections and tags (no application, no binder; at most 16 nodes), after substituting
the `let`s a compiled `match` makes for fields. `Bool.and`, `Bool.or`, `Bool.not`, a
`getD` or `orElse` on `Option` are. A call with all `n` arguments is compiled as the
`case` itself (`ETerm.caseInline` in `Wiz/Compiler/Inline.lean`, run on every reachable
definition by `compileReachableE`, before lowering):

* an argument whose parameter the scrutinee uses, or that more than one branch uses, is
  computed first, as before;
* an argument whose parameter one branch uses is computed in that branch;
* an argument whose parameter no branch uses is not computed.

A partial application (`foldB Bool.and`, a fold given the function) still calls the definition.

Why this is sound: the language is pure, so when an argument is evaluated cannot be
observed, only whether the program returns. The result is the same whenever the
call-by-value program returned. A program that did not return because of such an
argument (a `partial` definition that loops, an absurd case) now returns when the
branch taken doesn't use it, which is what the kernel's evaluator does with the same
term. An argument of type `IO A` is a value (a function of the world): not building it
performs nothing, and performing it was never part of evaluating the call.

The passes after it see ordinary `case`s: constant folding (15c) removes the `case`
when the test is known, the recursive call in a branch is a tail call and becomes a
loop (15f), and borrow inference and reuse (8e, 8f) run on the result.

    def mem (n : Nat) : List Nat → Bool
      | .nil => .false
      | .cons x xs => Bool.or (Nat.beq x n) (mem n xs)

    def mem @&x0 @&x1 :=
      join j1(x13 x14) :=
          case x14 of
          | 0 => let x6 := Bool.false; ret x6
          | 1 =>
              let x8 := proj 0 x14
              let x9 := proj 1 x14
              let x10 := prim nat.beq x8 x13
              case x10 of
              | 0 => jmp j1 x13 x9
              | 1 => let x12 := Bool.true; ret x12
      jmp j1 x0 x1

Allocations in the checked-heap interpreter, without and with the pass
(`compileReachable … (caseShapes := false)` turns it off; the programs are
`caseShapeSrc` in `Tests/Elab.lean`):

| program | before | after |
|---|---|---|
| `mem 3 (range 1000)`: a search in a list that exists | 1000 | 1000 (the same cells; a loop that stops at the fourth) |
| `reach 8 100 [1]`: each level `Bool.or (mem n xs) (reach … (double xs))` | 101 | 4 |
| `Bool.and (mem 2000 (range 1000)) (mem 5 (range 1000))` | 2000 | 1000 |
| `orElse (.some 4) (List.length (range 50 xs))`, `xs` of 100 elements | 151 | 101 |

Tests: group `backend` (the IR of `mem`, `allLt` and a user function; the counts
above), groups `c` and `llvm` (a second argument that never returns; ten million steps
of `Bool.or (Nat.beq i n) (upFrom n (i + 1))` on a 1 MB stack at `-O0`).

The self-hosted backend does the same for its own input (small case-shaped functions
inlined with lazy arguments, branch `agent/selfhost-demand-d`); `&&` and `||` as macros
that expand to matches (`agent/prelude-batch`) need neither.

