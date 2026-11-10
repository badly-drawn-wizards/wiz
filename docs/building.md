# Building, testing and CI

## Building and testing

```sh
lake build          # the library and the `wiz` executable
lake test           # all exercise tests; every case runs in its own process
lake test -- conv   # only the groups whose name starts with "conv"
lake test -- =c     # only the group named exactly "c"
lake test -- '=selfhost#0,3'          # only cases 0 and 3 of the group "selfhost"
lake test -- --list                   # the group names
lake test -- --list-cases =selfhost   # the selected cases: GROUP<tab>INDEX<tab>NAME
lake test -- --timings t.jsonl rig    # also append each case's time to t.jsonl
```

Every case prints its wall time (`✓ name (12.345 s)`), and every group its total.
`--timings FILE` (with `--shard NAME` as a label) appends one line of JSON per case:
`shard`, `group`, `index`, `case`, `seconds`, `ok`, and `notes`, which say which shared
programs the case used and built (`Tests.note`: `uses checker`, `built checker 331.2`;
the self-hosted checker and compiler are built by the first case that needs them and
kept under `/tmp`).

An unimplemented exercise shows up as `✗ ... not implemented yet (hit a sorry)`.

## Continuous integration

`nix develop` gives the toolchain the tests need besides Lean (see `flake.nix`): GMP and
LLVM's `llc` for the C and LLVM backends, Boehm GC for the self-hosted backend, a C
compiler, and elan, which installs the Lean in `lean-toolchain`. Entered at the
repository root, it writes this machine's paths to the uncommitted `grail.local.wiz`,
which grail and the test driver read (`Tests/Main.lean`; flags to `lake test -- …` win);
`wiz` takes flags. Nothing reads environment variables.

GitHub Actions (`.github/workflows/ci.yml`) runs on pushes and pull requests to
`solutions` and `master`. Every job runs in that dev shell (with the Cachix cache, when
one is configured); the elan toolchain and `.lake` (including Lake's artifact cache) are
cached between runs.

* **The solution tree** (`solutions`; recognised by its `--<sol` markers) runs the full
  suite in parallel shards, one job per entry of `.github/test-shards.json` (each entry
  is a list of `lake test` selectors). The build job checks that every group of
  `Tests/Main.lean` is in exactly one shard (`scripts/ci.py check-shards`, which checks
  every case after splitting), so **a new test group must be added to
  `.github/test-shards.json`** (one selector per line, sorted within its shard) and to
  the `groups` list at the end of its test module (`Tests/*.lean`, one group per line,
  sorted; `Tests/Main.lean` only concatenates the modules' lists). Both are laid out so
  that branches adding different groups don't touch the same lines. Each shard's job summary has a table of every case's time
  (three decimals), group subtotals and the shard's total; the `CI result` job sums the
  shards up (a table of shard totals and the grand total, and the 15 slowest cases) and
  uploads every case's time as the `test-timings` artifact.
* **Split shards.** A shard with `"split": N` runs as N jobs `NAME-1` … `NAME-N`, each a
  list of `=GROUP#I,J,…` selectors. `scripts/ci.py` balances the parts with the case
  times in `.github/test-timings.json`: the cases that use the same shared program (the
  self-hosted checker or compiler, which the first case that needs it builds) stay in
  one part, so each program is built once, and the other cases fill the parts up. A new
  case counts as its group's median, with the programs most of its group uses. The
  baseline holds only the split shards' cases, one per line.
  `scripts/ci.py plan` shows the parts and their
  estimates. To refresh the baseline from a CI run:
  `gh run download RUN -n test-timings && scripts/ci.py baseline timings.jsonl > .github/test-timings.json`.
* **The exercise tree** (`master`) checks that everything builds and that the test driver
  runs to its summary line; the failures are the exercises.
* **The bootstrap fixpoint** (`scripts/fixpoint.sh`: the stage-1 C of the toolchain
  equals its stage-2 C) runs weekly on `solutions`, or from "Run workflow" with
  `fixpoint` ticked. It takes a long time; run it locally with `nix develop -c
  scripts/fixpoint.sh`.
* **The Nix package** (the `nix package` job): `nix build .#wiz` builds `wiz` and
  `grail` with Lake and nixpkgs' Lean (the flake checks that it is the version in
  `lean-toolchain`), and wraps them with the toolchain as flags (`--cc`, `--cflags`,
  `--ldflags`, `--llc`, `--gc-cflags`, `--gc-ldflags`; flags you pass come later and
  win) and, for `wiz`, the packaged standard library as a module root after `./lib`. CI
  pushes it to the public Cachix cache `badlydrawnwizards` on pushes and on pull
  requests from this repository (which have the token). The tests still use Lake, whose
  artifact cache rebuilds only what changed.
* **The Wiz build caches.** Each test shard keeps what the suite builds from Wiz
  programs between runs: the elaboration cache (`lake test -- --cache ~/.cache/wiz …`),
  `.grail`, and the self-hosted checker and compiler that the tests compile
  (`/tmp/wiz-selfhost-*`). The cache key starts with a hash of everything the compiler
  is made of (the `.lean` files, Lean, `flake.lock`), and partial hits only come from the
  same compiler (the elaboration cache's own keys include the wiz binary's hash, but the
  test driver's grail runs use a fixed binary id and the `/tmp` programs a timestamp).

To run Wiz without a checkout or a Lean toolchain, with the binaries from Cachix:

```
nix run --option extra-substituters https://badlydrawnwizards.cachix.org \
  --option extra-trusted-public-keys badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI= \
  github:badly-drawn-wizards/wiz/solutions#wiz -- check hello.wiz
```

or `cachix use badlydrawnwizards` once and then `nix run
github:badly-drawn-wizards/wiz/solutions#wiz -- …` (`#grail` for grail; `wiz build FILE
-o OUT` works out of the box). Name the `solutions` branch: the default branch, `master`,
is the exercise tree, whose `wiz` is mostly stubs. The `--option`s count only for a
trusted Nix user (or with the cache in `nix.conf`); otherwise Nix builds wiz from source,
which takes a few minutes.
