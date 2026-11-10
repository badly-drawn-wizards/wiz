# Stage 9: the C FFI

## 9a: IO, machine types, foreign functions ✅

```
import IO
extern "strlen" (header := "string.h") strlen : String → Nat
def main : IO Unit := do
  IO.println "hello from Wiz";
  IO.println (Nat.toString (strlen "hello"))
```

* `lib/IO.wiz`: `IO A := (1 w : World) → A × World`. The world is a **linear token**:
  QTT's usage checking makes sure every action takes it and gives it back exactly
  once, so effects are ordered and nothing else is impure. (`let 1 (a, w') := …`
  splits linearly; `match` can't, because `ind` uses its methods ω times.) `Monad IO`
  makes `do` work.
* `extern "cname" (header := "h.h")? name : T` declares an axiom implemented by a C
  function. Marshalling follows `T`: `Nat` and `UInt64` ↔ `uint64_t`, `Float64` ↔
  `double`, `String` ↔ UTF-8 `char*`, `Bool` ↔ `int`, `Unit` ↔ `void`; a result in `IO`
  takes and returns the world. The backends emit a C wrapper per foreign function.
  Without a header, a prototype is generated from the Wiz type.
* `UInt64` and `Float64` are axioms whose operations are runtime functions, bound
  with `extern` (boxed raw words at runtime). The kernel doesn't compute with them.
* `wiz run` on `main : IO A` runs it. Foreign functions only run in compiled code
  (`#eval`/`#run` report them).

## 9b: importing C headers ✅

```
import IO
import_c "string.h"            -- C.strlen : String → IO Nat, …
import_c "math.h" (pure)       -- C.pow : Float64 → Float64 → Float64, …
```

`import_c "h"` binds every function of a header whose types can be marshalled, as
`C.name`, in `IO` unless the import is marked `pure`. The command line tool (and the
tests) run the header through `cc -E -P` first, since the frontend is pure. A parser
for a small C subset (`FFI/CParse.lean`) reads the prototypes and the typedefs they
use, and skips struct bodies, inline function bodies and GNU extensions. Variadic
functions and functions taking pointers other than `char*` (or function pointers,
or structs by value) are skipped. On glibc, `string.h` gives 66 prototypes and
`math.h` gives 620.

| #   | Where              | What                                              |
|-----|--------------------|---------------------------------------------------|
| 9.1 | `FFI/CParse.lean`  | `declarator`: pointers, names, parameter lists    |

## 9c: checked C glue ✅

```
import_c "string.h"
glue sumTo (n : Nat) : Nat := "uint64_t s = 0; for (uint64_t i = 0; i < n; i++) s += i; return s;"
glue twiceLen (s : String) : Nat := "return strlen(s) * 2;"
```

A `glue` function's body is C, in a **checked subset** (`FFI/CGlue.lean`): scalar
locals, assignments, `if`/`while`/`for`/`return`, arithmetic and logic on integers and
doubles, strings passed around, and calls to functions from imported headers (with
their types checked). Pointer dereference, address-of, casts, indexing, member access,
`goto`, `asm` and `sizeof` are rejected, so glue can't corrupt memory by itself. The
checked code is emitted into the program, with its headers, and bound like an
`extern`.

| #   | Where              | What                                     |
|-----|--------------------|------------------------------------------|
| 9.2 | `FFI/CGlue.lean`   | `expr`: types of glue expressions        |

## 9d: foreign pointers, finalizers, buffers ✅

```
foreign_type FILE (finalizer := "fclose")
extern "fopen" (header := "stdio.h") fopen : String → String → IO FILE
extern "fputs" (header := "stdio.h") fputs : String → FILE → IO Nat
```

* `foreign_type T (finalizer := "f")` declares an opaque type of C pointers. A pointer
  returned by a foreign function is wrapped in a reference-counted object, and `f` runs
  when the last reference goes. An argument is borrowed during the call and released
  after it. Glue code can pass foreign pointers on but not look inside them.
* `Bytes` (in `lib/IO.wiz`) is a byte buffer whose `push` updates in place when the
  buffer is unique (the same idea as Perceus reuse). It has `IO.readFile` for input.
  Runtime helpers like these take Wiz values as they are (the `w` marshalling kind).

The FFI is complete for now. Not done yet: callbacks (C calling Wiz closures), structs
by value, and mapping more of a header's pointer types onto foreign types automatically.

## 9e: linear sequencing ✅

```
axiom Tok : Type
axiom Tok.close : (1 t : Tok) → IO Unit
def finish (1 t : Tok) : IO Nat := do1
  IO.println "closing";
  Tok.close t;
  IO.pure 3
```

* `IO.bind` takes its action and its continuation **at quantity 1** (both are used
  once), so an action that consumes a linear value can be sequenced, and the
  continuation may capture one. Unrestricted arguments pass as before. `IO.then1 x y`
  runs `x`, drops its result, then `y`.
* `class Monad1 m` has `bind1 : (1 x : m A) → (1 f : A → m B) → m B`, and **`do1`** is
  `do` notation over it (`x ← e;`, `e;`, `let x := e;`). `do` stays on `Monad.bind`,
  whose continuation is unrestricted: the same block written with `do` is rejected
  when a later step uses a linear variable. Bound results are unrestricted in both.
* Transport for linear values: `Eq.cast (0 e : A = B) (1 a : A) : B`, `Eq.subst P e`
  and `Eq.substBack P e` take the transported value at 1 (the kernel's `cast` already
  passes its argument's usage through), e.g. `Chan (dual (dual p))` to `Chan p` given
  a proof (Prelude; plan L4).

## 9f: C source files and libraries ✅

```
link_c "term.c"                       -- relative to this .wiz file
link_lib "m"                          -- -lm
extern "iv_term_open" Term.open : IO Nat
```

* `link_c "f.c"` names a C file to compile and link with any program that imports the
  module (or is the file). The path is relative to the `.wiz` file that says it (a
  module's to the module's file), or absolute. It is the **unchecked** counterpart of
  `glue`: the file may use pointers, structs, system headers and static helpers; Wiz
  sees only the functions it binds with `extern`. A file named twice is linked once.
* `link_lib "m"` links a library (`-lm`), after the toolchain's `--libs`.
* `wiz build`/`wiz run` compile the files with the program, with the same compiler and
  `--cflags` (`-O2 -w`, like the generated C), through either backend (with `--llvm` the
  linking step compiles them). The frontend is pure, so the command line resolves the
  paths first (`Module.cSourceTable`, like the headers of `import_c`); a file that
  doesn't exist is an error at its `link_c`. The commands aren't cached (they rerun on
  every elaboration; they are cheap), so a file deleted later is still noticed. In the
  language server the paths aren't checked.
* grail (stage 23): `c F` lists the files and libraries in `link.txt` beside `main.c`;
  `link E` compiles and links them, and its key covers their paths, their contents and
  the `cflags`, so editing a C file reruns only the link (and the `run` tests that use
  the program). Which of the files exist enters `check F`'s key, so a deleted file is
  reported by the check.
* `--gmp "…"` (a toolchain field, default `-lgmp`; also `gmp` in `grail.local.wiz`) says
  how GMP is linked. For WebAssembly it is mini-gmp's C file, so `web/build.sh` is one
  `wiz --cc emcc --gmp ".../mini-gmp.c" build web/Web.wiz -o wiz-infoview.mjs`, with
  `web/js.c` (Emscripten's `EM_JS`) from `link_c "js.c"`. The terminal infoview links
  `infoview/term.c` (termios, poll, sockets) the same way.

Not done: `pkg-config` names (`link_pkg "gtk+-3.0"`) — for now, give their flags with
`--cflags`/`--ldflags`.
