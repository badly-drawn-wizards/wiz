# Stage 23: grail, a build tool

## 23b: modules by path ✅

`import A.B` reads `A/B.wiz` under the first **module root** that has it; `lib/` is a
root, so `import Prelude` is `lib/Prelude.wiz` as before. The frontend stays pure: the
caller reads every module a file can reach up front, by scanning its import lines
(`Wiz/Module.lean`).

## 23c: a key per module, atomic writes ✅

A module's key is computed from text alone, before anything is elaborated:

    key(M) = hash(salt, toolchain, text of M, M's C headers, key(N) for each import N)

and a module is elaborated **in isolation**, from the empty state plus its own imports,
so what it elaborates to depends only on its key. An importer's chain of command keys
mixes in `key(M)` at the `import`. Editing a module now invalidates it and what imports
it, not the whole library, and a module imported by many files is cached once. A module
that uses a name it doesn't import is an error, with the cache or without (`--no-cache`
keeps the effects in memory for the run), and in `runFrontend`, which the tests and the
language server use: it checks each module once in isolation (errors are reported at
the `import`) and then elaborates it into the importer's state, unless that state is
still the initial one and the isolated result serves as it is. So the editor rejects
what `wiz check` rejects. Cache files are
written to a temporary name and renamed, so concurrent runs never see half a file.

## 23d: grail v0 ✅

A package is a directory with a `grail.wiz`, written in Wiz against `lib/Grail.wiz`:

```
import Grail
def package : Package := Package.new "wiz"
  |> Package.lib "std" "lib"                    -- check every module under lib/
  |> Package.check "app" "app.wiz"              -- check one file
  |> Package.exe "io" "examples/io.wiz"         -- compile `main`: .grail/bin/io
```

```sh
lake build grail
.lake/build/bin/grail build          # every target; `grail build std` for one
.lake/build/bin/grail targets        # list them; `grail config` prints the toolchain
```

grail evaluates `Package.render package` (an S-expression) in the interpreter and
builds a graph of **jobs**: `check` per file, and `ir → c → obj → link` per executable.
A job's key is computed from its inputs before it runs (a check from the file's key, an
object from the C text and the compiler flags), its output goes to
`.grail/build/<key>/` through a temporary directory and a rename, and a job whose
directory exists doesn't run: **a second build runs no jobs**, an edit reruns the checks
of the files that import what changed, and an edit that leaves the C alone stops there.
The key also covers the grail binary itself, so a new elaborator rebuilds everything.

There are no environment variables: the C compiler and its flags come from flags
(`--cc`, `--cflags`, `--ldflags`, `--llc`, `-I DIR`, `--cache DIR`, `--no-cache`) or from
an uncommitted `grail.local.wiz` with this machine's paths (`nix develop` writes it from
`flake.nix`):

```
import Grail
def settings : Settings := Settings.empty
  |> Settings.set "cflags" "-I/nix/store/…-gmp-…-dev/include"
  |> Settings.set "ldflags" "-L/nix/store/…-gmp-…/lib -Wl,-rpath,/nix/store/…-gmp-…/lib"
```

## 23a: the toolchain as flags ✅

`wiz` reads no environment variables: the toolchain record (`Wiz/Toolchain.lean`: C
compiler and flags, `llc`, the collector's flags, the cache, module roots) comes from
`--cc`, `--cflags`, `--ldflags`, `--libs`, `--llc`, `--cache DIR`/`--no-cache` and
`-I DIR` (which replaces `$WIZ_PATH`), and is passed explicitly to everything that
compiles. Its compiler fields are its `id`, which enters grail's keys.

## 23e: the self-hosted toolchain as targets ✅

`Package.selfhost NAME ROLE` builds the self-hosted programs from `selfhost/*.wiz`
(`Wiz/Selfhost.lean` generates their sources, parser tables included, for grail and the
tests alike): `checker`, `compiler`, and `bootstrap`, the fixpoint check of
`scripts/fixpoint.sh` as jobs (generate the source, build stage 1, `self1.c`, stage 2,
`self2.c`, compare). `grail build bootstrap` runs it (minutes); run again, it runs
nothing unless a source, `rt.c`, the toolchain or grail changed. `grail build` alone
leaves it out.

## 23f: a test runner ✅

`Package.tests NAME DIR` makes every `.wiz` file under `DIR` a test, with its expected
output beside it in `.expected`. The first line gives the kind: `-- test: check` (the
default: the messages, as `wiz check` prints them) or `-- test: run` (what `main` prints,
compiled through C). A pass is a job like any other, keyed by the file (and its
imports), the kind, the toolchain and the expected output, so `grail test` again runs
nothing; `grail test FILTER` runs the tests whose path contains it, and
`grail test --update` writes the actual output. Every example is a test
(`examples/*.expected`). The Lean tests stay in `lake test`.

## 23g: parallel jobs ✅

The jobs form an explicit graph (`Grail/Graph.lean`): `ir F` depends on `check F`, …,
`link E` on `obj F`, a check on the checks of the package modules it imports, a `run` test
on its executable, the bootstrap steps on each other. A node's key is computed when its
dependencies are done (an object's key hashes the C its `c` node wrote); a node whose
output exists is up to date, the rest are jobs in a ready queue. `grail build -j N`
(default: the cores, at most 4) runs up to `N` jobs at a time, each as a separate process
(`grail --grail-job …` with the toolchain as flags, or the C compiler) under `timeout`
(`--timeout SECS`, default 1800; tests `--test-timeout SECS`, default 300, so a test that
hangs fails instead of hanging the run). A failed job is reported and the jobs that depend
on it are skipped; the others still run. Each job's output is buffered and printed in the
graph's order, so `-j 1` and `-j 8` print the same report, and a second build still runs
no jobs.

## 23h: git dependencies and a lock file ✅

`Package.dep NAME URL REV` depends on the package at a git URL (a path, `file://`,
`https://`) and revision (tag, branch or commit). `grail update` resolves each
dependency, and theirs (from their own `grail.wiz`), to a commit, clones it to
`.grail/packages/NAME`, and writes `grail.lock`, which is committed:

```
(lock
  (dep greet "https://example.org/greet.git" v1 88bef64fe0c79f190976221e57f65d6b17a1866c 89d8a320ea2473de))
```

(name, URL, revision, commit, and a hash of the checked-out files). Builds use the lock
only: each dependency is checked out at its locked commit (fetched if missing), files
that don't match the hash are refused, and a `REV` changed in `grail.wiz` stays at the
locked commit, with a note, until `grail update`. The roots of a dependency's `lib`
targets become module roots, so `import Greet.Hello` finds
`.grail/packages/greet/src/Greet/Hello.wiz`; module keys already hash module texts.
Two different commits of one dependency name are refused (no version resolution yet).
