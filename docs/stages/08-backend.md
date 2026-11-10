# Stage 8: the backend

## 8a: IR and Perceus reference counting ✅

```
#ir twice          -- def twice x0 x1 :=  dup x0;  let x2 := ap x0 x1;  let x3 := ap x0 x2;  ret x3
#run fact 10       -- 3628800, through the IR, on a heap that checks reference counts
```

* **IR** (`Compiler/IR.lean`): A-normal form, first order: objects (`ctor`), fields
  (`proj`), direct calls (`fap`), closures (`pap`/`ap`), native operations (`prim`),
  `case` on tags, join points. Constructors without fields and numbers are unboxed
  scalars.
* **Lowering** (`Compiler/Lower.lean`): lambda lifting, closure conversion, arities,
  join points for non-tail `case`s (closed over their variables). The generic
  eliminators are written in the erased language (`Compiler/PrimCode.lean`) and
  compiled like user code. The output is sorted by name, so it's deterministic.
* **Perceus** (`Compiler/RC.lean`): every variable is owned; `dup` an argument that
  is still needed, and `drop` a variable as soon as it's dead (garbage free).
* **Checked heap** (`Compiler/IRRun.lean`): `#run` runs the IR with explicit reference
  counts and fails on use after free, double free, or leaks. All the examples give the
  same results under `#run` as under `#eval`.

| #   | Where             | What                                     |
|-----|-------------------|------------------------------------------|
| 8.1 | `Compiler/RC.lean`| `insertRC`: Perceus `dup`/`drop`        |

## 8b: C ✅

```
$ wiz run fact.wiz        # def main : Nat := fact 30
265252859812191058636308480000000
```

* `wiz build FILE -o OUT` compiles the definition `main` to C and then to an
  executable; `wiz run FILE` also runs it and reads the printed result back with
  `main`'s type. The C compiler is `--cc X` (default `cc`), with `--cflags "…"` and
  `--ldflags "…"` for GMP ([stage 23a](23-grail.md): flags, not environment variables). The C tests
  skip themselves if GMP isn't found.
* **Runtime** (`runtime/wiz.c`, embedded in the compiler): a value is a word; scalars
  have the low bit set; objects have a header (reference count, tag, size). Closures
  point to a boxed entry and share or move their captured arguments when applied.
  Numbers that don't fit in 62 bits are GMP integers. Projecting a number gives its
  unary view. The program checks at exit that every object was freed.
* **Codegen** (`Compiler/C.lean`): one C function per IR function (plus a boxed
  version for closures); `case` is a `switch`, join points are labels, `dup`/`drop`
  call the runtime.

| #   | Where              | What                                   |
|-----|--------------------|----------------------------------------|
| 8.2 | `Compiler/C.lean`  | `body`: C statements for an IR body    |

## 8c: reuse ✅

`Compiler/Reuse.lean` pairs each `drop x` with a later allocation in the same block:
`let w := reset x; …; let y := reuse w in ctor t args`. At runtime, if `x` was unique,
its fields are dropped and the new object is written into its cell (if the sizes
match), so updating data you own happens in place. Constructor functions are inlined
when fully applied, so user code takes part. The generic eliminators already reuse
their payload pairs.

A cell is often taken apart in one block and rebuilt in another: a tree node is
projected and dropped at once, but the new node is built two `case`s later, after
comparing keys. So `reuseAcross` runs first and follows a dropped cell into the
branches (as Perceus and Lean 4 do): the `reset` stays where the drop was, each branch
that builds an object reuses the token, and the others free it at once
(`reuse w in ctor 0`, which needs no cell). The IR has no types, and a `Bool` returned
by a function has no cell to give, so only variables known to be objects (projected
from, or built) go across, outermost first; the local pass pairs what is left. A
zipper's insertion loop then allocates nothing per level.

| #   | Where                 | What                                          |
|-----|-----------------------|-----------------------------------------------|
| 8.3 | `Compiler/Reuse.lean` | `insertReuse`: pair drops with allocations    |

## 8d: LLVM ✅

`wiz build FILE -o OUT --llvm` and `wiz run FILE --llvm` go through textual LLVM IR
(`Compiler/LLVM.lean`) and `llc` (`--llc X`). The runtime is the same C file,
compiled separately with `-DWIZ_API=` so that its functions are exported. In SSA form,
join point parameters live in stack slots, and a variable bound in several branches
gets one name per branch. The LLVM tests are the C tests, through LLVM.

Still to do in the backend: specialise the eliminators for known descriptions (flat
constructor objects instead of nested pairs, direct recursion instead of walking the
description), borrowed parameters, and drop specialisation.
