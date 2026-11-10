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
