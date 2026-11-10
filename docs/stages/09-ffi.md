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

## 9h: system interfaces: processes, environment, files ✅

```
import Sys
def main : IO Unit := EIO.toIO (do
  o ← Process.output "cat" .nil "piped through cat\n";
  EIO.lift (IO.print o.stdout);
  Env.set "GREETING" "hi";
  d ← FS.createTempDir;
  FS.writeFile (Path.join d "a.txt") "alpha\n";
  names ← FS.listDir d;
  FS.removeAll d)
```

`lib/Sys.wiz` binds the POSIX interfaces a program needs to drive other programs
(what the toolchain manager and grail need, see stages 23 and 26), with C in the
runtime's section "system interfaces" (`runtime/wiz.c`, so both backends have it).

* **Errors.** Anything that can fail returns `EIO A := IO (Except String A)`, a monad of
  its own, so a `do` block stops at the first error; `EIO.lift` runs an `IO` action in
  it and `EIO.toIO` runs it as `main`, printing the error to stderr and exiting with 1.
  An error reads `"<path or call>: <strerror(errno)>"`. Underneath there are two
  shapes of foreign function: a call that only succeeds or fails returns the errno
  (0 for success, `Sys.lift`), and a call that returns a value records its errno per
  thread, read back by `Sys.errno` right after it (`Sys.check`; the linear world
  token keeps the two calls together and in order). Results that are lists (directory
  entries, the environment, a `stat`) are built by the runtime as Wiz lists.
* **Environment.** `Env.get : String → IO (Option String)`, `Env.set`, `Env.unset`,
  `Env.list : IO (List (String × String))` (sorted by name). Setting variables isn't
  thread-safe in C: set them before starting threads.
* **Files and directories** (`FS.`). `currentDir`, `setCurrentDir`, `createDir`,
  `removeDir`, `removeFile`, `removeAll` (recursive, doesn't follow links), `rename`,
  `symlink target link`, `readLink`, `setMode`, `listDir` (sorted, without `.` and
  `..`), `stat` and `linkStat` (a `FileStat`: kind, size, modification time, mode),
  `exists`, `isDir`, `isFile`, `tempRoot` (`$TMPDIR` or `/tmp`), `createTempDir`
  (`mkdtemp`), and whole files: `readFile`, `writeFile`, `appendFile`, and `readBytes`,
  `writeBytes` for binary data (text stops at a NUL byte). `Path.join` puts a `/`
  between two paths.
* **File handles.** `foreign_type File` (closed by its finalizer, or `File.close`):
  `File.open path mode` (`fopen` modes), `File.stdin`/`stdout`/`stderr`,
  `readLine` (`none` at the end), `readAll`, `write`, `flush`. `IO.ePrintln` prints
  to stderr.
* **Processes.** `Process.spawn cmd args stdin stdout stderr` starts `cmd` (searched in
  `PATH`, `posix_spawnp`) with each stream `.inherit`, `.piped` or `.null`, giving a
  `Child` (a foreign type: its pipes close and a finished child is reaped when it
  goes). `Child.write`, `closeStdin`, `readStdout`/`readStderr` (to the end),
  `communicate input` (writes stdin while collecting stdout and stderr with `poll`, so
  a child that fills one pipe doesn't deadlock), `wait` (an `ExitStatus`: `exited code`
  or `signaled n`), `kill`, `pid`. `Process.output cmd args input` runs a command to the
  end and returns its status and output; `Process.run` runs one with this program's
  streams; `Process.exec` replaces the program; `Process.exit`, `Process.id`. The
  runtime ignores `SIGPIPE` once a child has been started (a write to a closed pipe is
  then an `EPIPE` error), and the pipes are close-on-exec, so other children don't keep
  them open.
* `#eval` and `#run` can't do any of this (they are pure and can't call C): there are
  no models for system calls, since a model of the file system or of processes would
  give answers the real program wouldn't. The pure helpers (`Path.join`,
  `ExitStatus.ofNat`, `FS.statOf`, `Env.pairs`) run anywhere.

Tests: the `sys` group (spawning `echo`, a pipe through `cat`, exit codes and spawn
errors, the environment, a temporary directory's life: files, links, stat, listing,
removal, handles), on both backends.
