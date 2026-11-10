# Building, testing and CI

## Building and testing

```sh
lake build          # the library and the `wiz` executable
lake test           # all exercise tests; every case runs in its own process
lake test -- conv   # only the groups whose name starts with "conv"
lake test -- =c     # only the group named exactly "c"
lake test -- --list # the group names
```

An unimplemented exercise shows up as `✗ ... not implemented yet (hit a sorry)`.

## Continuous integration

`nix develop` gives the toolchain the tests need besides Lean (see `flake.nix`): GMP and
LLVM's `llc` for the C and LLVM backends, Boehm GC for the self-hosted backend, a C
compiler, and elan, which installs the Lean in `lean-toolchain`. Entered at the
repository root, it writes this machine's paths to the uncommitted `grail.local.wiz`,
which grail and the test driver read (`Tests/Main.lean`; flags to `lake test -- …` win);
`wiz` takes flags. Nothing reads environment variables.

GitHub Actions (`.github/workflows/ci.yml`) runs on pushes and pull requests to
`master`. Every job runs in that dev shell (with the Cachix cache, when
one is configured); the elan toolchain and `.lake` (including Lake's artifact cache) are
cached between runs.

* **The test suite** runs in parallel shards, one job per entry of `.github/test-shards.json` (each entry
  is a list of `lake test` selectors). The build job checks that every group of
  `Tests/Main.lean` is in exactly one shard (`scripts/ci.py check-shards`), so **a new
  test group must be added to `.github/test-shards.json`**. Each shard prints a pass/fail
  table in its job summary, and the `CI result` job sums them up for the whole suite.
* **The exercise tree** (the `exercise tree` job) is generated with
  `scripts/mkexercises.py` into a temporary directory and built (`lake build wiz grail
  tests`), with a Lake cache of its own; it runs beside the test shards. It does not run
  the exercise tree's tests (almost all of them fail by design). See
  [exercises.md](exercises.md).
* **The bootstrap fixpoint** (`scripts/fixpoint.sh`: the stage-1 C of the toolchain
  equals its stage-2 C) runs weekly on `master`, or from "Run workflow" with
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
  github:badly-drawn-wizards/wiz#wiz -- check hello.wiz
```

or `cachix use badlydrawnwizards` once and then `nix run
github:badly-drawn-wizards/wiz#wiz -- …` (`#grail` for grail; `wiz build FILE -o OUT`
works out of the box). Without a branch the flake reference means the default branch,
`master`, whose binaries are on Cachix once its `nix package` job has run. The
`--option`s count only for a trusted Nix user (or with the cache in `nix.conf`);
otherwise Nix builds wiz from source, which takes a few minutes.

`#nvim-wiz` is Neovim with the Wiz plugin (editors/nvim, docs/stages/11-tooling.md
11p) and this wiz on `PATH`: `nix run github:badly-drawn-wizards/wiz#nvim-wiz --
file.wiz`. `packages.<system>.wiz-nvim` is the plugin alone, for a Neovim
configuration in Nix.
