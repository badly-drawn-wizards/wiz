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
after the call): otherwise the call stays a call.
