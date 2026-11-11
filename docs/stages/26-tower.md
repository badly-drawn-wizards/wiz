# Stage 26: tower, a toolchain manager

tower is to Wiz what elan is to Lean (and rustup to Rust). It installs Wiz toolchains
(`wiz`, `grail`, the standard library, the editor plugins) by channel or version, and
puts **shims** named `wiz` and `grail` on `PATH`. A shim runs the toolchain the current
directory asks for. The editor plugin starts `wiz lsp` from `PATH`, and grail runs the
`wiz` it finds there, so both get the project's toolchain without any setup of their own.

## 26a: specs, project files, overrides ✅

A **spec** names a toolchain:

| spec | means |
|---|---|
| `nightly` | the tip of the branch `nightly-ref` (default `master`) |
| `stable` | the highest `vX.Y.Z` tag |
| `v0.2.0`, `my-branch`, a commit | that tag, branch or commit |
| `REF@COMMIT` | that commit (`master@6f29a0a…`); the ref is a label |
| a linked name | a toolchain made by `tower toolchain link` |

A project names its toolchain in a file **`wiz-toolchain`** at its root (one line, a
spec; lines starting with `#` or `--` are comments), the same way `lean-toolchain` works
for Lean. It's a separate file rather than a field of `grail.wiz`: tower then never has
to evaluate Wiz, and directories that have no grail package can use one too.

Which toolchain runs (`tower show` says which, and why):

1. `wiz +SPEC …`: a first argument starting with `+` (as with rustup);
2. else, walking up from the current directory, an **override** for that directory
   (`tower override set SPEC [DIR]`, kept in the settings), or a `wiz-toolchain` file
   in it. The first directory with either one wins;
3. else the **default** (`tower default SPEC`).

## 26b: sources ✅

Installing first resolves the spec to a commit with `git ls-remote` on the `git`
setting, then realises it from one of three sources:

* **nix**: `nix build FLAKE/COMMIT#wiz`, the package from the flake (`packages.wiz`),
  which comes from the Cachix cache `badlydrawnwizards` when your Nix user is trusted
  (tower passes the substituter, as in docs/building.md). The store path is linked as
  `toolchains/NAME/nix`, which is a GC root. `bin` and `share` point into it.
* **release**: `RELEASES/TAG/wiz-ARCH-linux.tar.gz` from GitHub Releases (26d) for a
  tag (and `stable`); for anything else, a commit, `REF@COMMIT` (`master@<sha>`), a
  branch or `nightly`, the snapshot of its commit, `RELEASES/snapshot-<sha>/…` (26g).
  It is checked against its `.sha256`, which a snapshot must have. A commit without a
  snapshot is an error that lists the retained snapshots and the other sources.
* **source**: `git clone`, then `lake build wiz grail` (this needs elan), then the build
  is copied into the layout below and the clone is removed.

`--source auto` (the default, the `source` setting) tries nix when `nix` runs, then the
release, then the source, and moves on to the next when one fails.
`tower update` re-resolves channels and branches and reinstalls the ones that moved,
using the source and flags they were installed with.

## 26c: layout, wrappers and shims ✅

```
~/.tower/
  settings                 `tower settings`, `tower set KEY VALUE`
  bin/wiz, bin/grail       the shims; bin/tower (`tower self install`)
  toolchains/NAME/
    bin/wiz, bin/grail       run these: the binary with the toolchain's flags
    share/wiz/lib/           the standard library
    share/wiz/.lake/build/bin/{wiz,grail}   the binaries (grail finds lib/ from here)
    share/wiz/editors/       the editor plugins, when the source has them
    share/wiz/TOOLCHAIN      a marker: editors find the toolchain a library file belongs to
    tower.info               spec, source, ref, commit, flags
```

This is the layout of the Nix package (`$out/share/wiz` looks like a checkout), so a Nix
toolchain is just links into the store. A toolchain is built in
`toolchains/.tmp-…` and renamed into place, so a shim never sees half of one.

**Flags, not environment variables** (stage 23a). The wrappers `bin/wiz` and
`bin/grail` of a release, source or linked toolchain are generated `sh` scripts. They
`exec` the binary with the C toolchain as flags (`--cc`, `--cflags`, `--ldflags`,
`--libs`, `--llc`, `--gc-cflags`, `--gc-ldflags`: the `tower set cflags …` settings,
overridden by `tower toolchain install … --cflags …`), and `wiz` also gets
`-I share/wiz/lib`. This is the same thing the Nix package's `makeWrapper` does. With no
flags set, `wiz build` uses `cc` and the system's GMP.

**The shims** are generated `sh` scripts too:

```sh
case "$1" in
  +*) tc=$('/home/me/.tower/bin/tower' --home '/home/me/.tower' resolve "$1") || exit; shift ;;
  *) tc=$('/home/me/.tower/bin/tower' --home '/home/me/.tower' resolve) || exit ;;
esac
exec "$tc/bin/wiz" "$@"
```

`tower resolve` prints the toolchain's directory, installing it first if needed
(`tower set auto-install false` turns that off). It writes its notes to stderr, so a
first `wiz lsp` still works. Because the shim `exec`s, the process that keeps running is
the toolchain's own `wiz`, which is what the language server's stdio, signals and exit
codes need. The shims are scripts rather than tower itself under another name (elan
uses one binary for everything) because a Lean program can't see its `argv[0]` and
can't `exec`. A script costs one `sh` and one quick tower run per call.

**Why tower was written in Lean** (it is now also written in Wiz, 26e). Wiz programs could read their arguments (`IO.args`,
21k), but they couldn't start or `exec` processes, read environment variables, list,
rename or link files, or set file modes. tower needs all of these, and grail is written
in Lean for the same reason. tower is its own small library (`Tower/`, which doesn't
import Wiz) and its own Lake executable, so its Nix package builds in seconds.

Commands:

```
tower toolchain install SPEC… [--source auto|nix|release|source] [--force] [--cflags …]
tower toolchain uninstall NAME… / toolchain list
tower toolchain link NAME DIR      a checkout (DIR/.lake/build/bin) or a toolchain dir
tower default [SPEC]               (installs it)
tower override set SPEC [DIR] / override unset [DIR] / override list
tower show / which wiz / run SPEC -- CMD…   (run: SPEC's bin/ first on PATH)
tower update [NAME…]
tower set KEY VALUE / settings     source flake git releases nightly-ref auto-install cc cflags …
tower self shims / self install    [--self PATH: the tower the shims call]
```

`tower toolchain link dev ~/src/wiz` points the toolchain `dev` at a checkout's
`lake build`. Put `dev` in a project's `wiz-toolchain`, or run `wiz +dev …`, to try a
compiler you are working on.

## 26d: installing tower, release tarballs ✅

**With Nix**: the package (`packages.tower`) contains tower and the `wiz` and `grail`
shims, which call that same tower; installing it puts all three on `PATH`:
`nix profile install github:badly-drawn-wizards/wiz#tower` (or `home.packages` /
`environment.systemPackages`), then `tower default nightly`. Nix installs only tower and
the shims: the toolchains are installed by tower into `~/.tower` (with `tower set source
release` they come from the release tarballs and never from Nix). The package adds git,
tar and curl to tower's `PATH`; `nix` and `lake` are yours. `tower self shims` is still
there for shims in `~/.tower/bin` (they then call the tower given with `--self`).

**With the install script** (no Nix):
`curl -sSfL https://raw.githubusercontent.com/badly-drawn-wizards/wiz/master/scripts/tower-init.sh | sh`
(or `| sh -s -- v0.2.0` for a tag). It downloads the tarball, runs `tower self install`
and then `tower default nightly`.

**From a release tarball**: unpack `wiz-x86_64-linux.tar.gz`. Its `bin/` already works
on its own (`bin/wiz`, `bin/grail` and `bin/tower`). Then run
`wiz-x86_64-linux/bin/tower self install`, which copies tower to `~/.tower/bin` and
writes the shims, followed by `tower default stable` (or `nightly`).

`.github/workflows/release.yml` builds the tarball (`scripts/release-tarball.sh`) outside
Nix with elan's Lean. The binaries then depend only on glibc (2.27 or later) and the C
runtime, as Lean's own releases do, and the job checks that no `/nix/store` path is
linked in. It runs on:

* tags `vX.Y.Z`: a GitHub release with the tarball and its `.sha256`;
* pushes to `master`: the snapshot of the commit; the tag `nightly` moves to it once
  CI has passed on it (26g);
* pull requests that touch the packaging: the tarball is built and tested, but nothing
  is uploaded.

The job also checks and compiles `examples/io.wiz` with the unpacked tarball on plain
Ubuntu, and installs the tarball through tower from a local release directory.
`wiz build` and grail need a C compiler and GMP (`apt install gcc libgmp-dev`); the
self-hosted toolchain also needs the Boehm collector (`libgc-dev`, with `tower set
gc-ldflags "-lgc -lpthread"`).

**Editors.** wiz.nvim starts `wiz lsp` with the root directory as its working
directory, so the shim picks that project's `wiz-toolchain`. `share/wiz/editors/nvim`
(release and source toolchains) is the plugin that matches the toolchain:
`vim.opt.rtp:append(vim.fn.trim(vim.fn.system 'tower which wiz'):gsub('/bin/wiz$', '') .. '/share/wiz/editors/nvim')`.
`wiz-toolchain` is one of the plugin's root markers.

**Tests** (`lake test -- tower`, all offline). The upstream is a local bare repository
holding a tiny Lake project whose `wiz` and `grail` print their arguments, with a tag
`v1` and a moving `main`. The cases:

* resolution order, settings and version ordering;
* a source install with flags baked into the wrappers, then shims with a
  `wiz-toolchain` file, `+nightly` installing on first use, an override beating the
  file, `run`, `update` moving `nightly` but not `v1`, `uninstall`, and `auto-install
  false`;
* a release install from a tarball made by `scripts/release-tarball.sh` (which works on
  its own), a refused checksum, no release for a branch, and `link` plus `default` of an
  unpacked tarball;
* snapshots (26g): full and short pinned commits, a bare commit with `auto`, a `keep/`
  tag as a spec, a snapshot without its checksum refused, `nightly` following its tag
  while the branch is ahead (and `update` leaving it alone), and the error for a commit
  with no snapshot;
* a Nix install from a local flake whose package is a plain directory (no nixpkgs),
  linked as a GC root and unlinked by `uninstall` (skipped when there is no `nix`).

The shims in the tests call the test driver (`tests --tower …`), which runs tower.

## 26e: tower in Wiz ✅

`tower/` is tower again, in Wiz: a grail package (`tower/grail.wiz`) whose executable
`tower` (`cd tower && grail build`: `.grail/bin/tower`) has the same commands, messages,
settings file, `tower.info` and layout as the Lean one, module for module
(`Tower/Basic.wiz`, `Install.wiz`, `Cli.wiz`). It uses `lib/Sys.wiz` (9h, 9k) for processes,
the environment and files (`FS.realPath`, `IO.appPath`, and `SpawnOptions` for a child's
working directory and for `lake build` without the Lean variables), and `lib/Text.wiz`
(9j) for text; no C of its own. `grail test` in `tower/` checks the pure
functions (`tests/pure.wiz` against `tests/pure.expected`).

**Tests.** The cases of `Tests/Tower.lean` run tower as a process, through its command
line only, against either implementation: group `tower` against the Lean one (the test
driver, `tests --tower`), group `tower-wiz` against `tower/`, which the group's first case
builds with grail in `.lake/build/tower-wiz` (about 10 s from clean; later cases find it
up to date) and whose `grail test` it runs. The Wiz tower follows 26g too: release
snapshots of commits (short shas through the `snapshot-*` tags, the `.sha256` required),
`nightly` as the commit of the tag `nightly`, `keep/` tags as specs, release in the `auto`
candidates, and the same error for a commit without a snapshot.

The Lean tower is still what the flake (`packages.tower`) and the release tarball ship.
Switching means: `packages.tower` builds `tower/` with grail (the `wiz` package plus GMP
and a C compiler at build time instead of Lake: the binary then links GMP, so the
package's closure grows by GMP and glibc only), `scripts/release-tarball.sh` takes the
grail-built binary (it is linked against the system GMP like `wiz build` output, so the
tarball's "glibc and the C runtime only" promise needs a static GMP or `--gmp` with
mini-gmp), the `--tower` mode of the test driver and `Tower/` go, and the group `tower`
is dropped in favour of `tower-wiz`.

## 26g: release snapshots for every master commit ✅

A project that pins a commit (`master@<sha>` in `wiz-toolchain`) can be installed
without Nix: every master push publishes the tarball of that commit.

**Snapshots.** For each push to master, `.github/workflows/release.yml` builds and tests
the tarball as before. Then `scripts/release-snapshots.sh publish` creates the
pre-release `snapshot-<full sha>` (its tag points at the commit) with
`wiz-x86_64-linux.tar.gz` and its `.sha256`. `gh release create` makes a draft, uploads
the files and then publishes it, so the tag appears only once the files are complete.
There is one release per commit rather than one release that holds every commit's files,
because then tower needs neither the GitHub API nor a token: `git ls-remote` lists the
`refs/tags/snapshot-*` that exist (this also expands a short sha and gives a clear
error), and a full sha names its URL,
`releases/download/snapshot-<sha>/wiz-x86_64-linux.tar.gz`. GitHub sets no limit on the
number of releases or on their total size (only on each file, 2 GiB, and on the files of
one release, 1000), so pruning (below) keeps the size in check. Pull requests that touch
the packaging still build and test the tarball, and they also run
`scripts/test-release-snapshots.sh`, but they publish nothing.

**nightly is a tag.** It moves only to a commit whose CI passed: master can break even
though every merged PR was green (two PRs green alone, in semantic conflict). A snapshot
of a red commit may exist, since pins name commits explicitly, but `nightly` (what
users get by default) never points at one. `.github/workflows/nightly.yml` runs when
the CI workflow completes successfully on a master push (`workflow_run`). It waits up to
an hour for that commit's `snapshot-<sha>` tag, because release.yml runs alongside CI,
and stops at once if no release.yml run of the commit is still going (one that failed,
or was cancelled by a newer push). Then it moves the tag, and only forwards: a commit
that is not ahead of the tag (an older run) leaves it. A ref update is atomic, so tower, which resolves `nightly` through
`git ls-remote` to the tag's commit and downloads that snapshot, can't hit a missing
file. Before, the assets were replaced in place, and downloads returned 404 while they
uploaded. The tag lags the branch by at least one CI run. A release install of
`nightly` records the tag's commit, and `tower update` compares against the tag, not
against the branch. The release `nightly` (`releases/download/nightly/…`, for people and
older towers) then gets the snapshot's files: each file is uploaded under a temporary name,
the old one is deleted and the new one renamed, so it is missing for one API call
instead of for a whole upload. `scripts/tower-init.sh` uses the snapshot of the tag
when `git` is there, and checks the `.sha256`.

**Retention.** After each publish, pruning keeps the newest 20 snapshots
(`SNAPSHOT_KEEP`; about 2.7 GB at 135 MB a tarball, see 26f), plus every snapshot whose
commit a `v*` tag, a `keep/…` tag or `nightly` points at. The others are deleted
together with their tags. **To keep a pinnable toolchain, push a keep/ tag**:
`git tag keep/icestick <sha> && git push origin keep/icestick`. Its snapshot then
outlives the window, and `tower toolchain install keep/icestick` works too, because a
`keep/` tag is a spec for its commit's snapshot.

**Older commits.** Running the workflow by hand (`workflow_dispatch`) with the input
`commit` set to a full master sha builds that commit and publishes its snapshot (nightly
does not move): `gh workflow run release.yml -R badly-drawn-wizards/wiz -f
commit=<sha>`, or "Run workflow" on the Actions page. The commit's tarball is laid out
by the workflow's current `scripts/release-tarball.sh`, not by the commit's own copy. A
dispatched snapshot is new, so it survives the next 20 pushes; push a `keep/` tag to
keep it for good.

**A commit with no snapshot** (never published, pruned, or not on master) fails with
`no release snapshot of commit <sha>`. The error lists what is retained (nightly and
the `keep/`/`v*` snapshots, with their commits, and how many recent ones there are) and
the alternatives: `--source source` (builds with elan), `--source nix`, or dispatching
the workflow for that commit. With `--source auto` tower falls through to the next
source.

