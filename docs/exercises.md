# Exercises and solutions

Wiz is also a course: each stage leaves parts of the implementation as exercises, and the
test suite tells you when you've got them right. The repository (the `master` branch)
holds one tree with the solutions in it; the exercise tree is generated from it on demand.

## The two trees

* **The solution tree** (the repository, `master`) is the complete implementation. Every
  exercise is a marked block whose solution and exercise versions sit side by side.
* **The exercise tree** is generated from it by `scripts/mkexercises.py SRC DST`: each
  marked block is replaced by its exercise version. It is not committed anywhere; make
  your own from a checkout:

  ```sh
  git clone https://github.com/badly-drawn-wizards/wiz && cd wiz
  scripts/mkexercises.py . ../wiz-exercises   # a new or empty directory
  cd ../wiz-exercises && git init && git add -A && git commit -qm "Exercises"
  nix develop -c lake build                   # then work through `lake test`
  ```

  The `git init` is optional, but with it a later run (`scripts/mkexercises.py .
  ../wiz-exercises` from an updated checkout) updates the tree in place: it refuses to
  run on a worktree with uncommitted changes, so commit your work first, then merge the
  new stubs with your answers using git.

  Until 2026-11-10 the exercise tree was the `master` branch, regenerated after every
  merge, and the solution tree was the `solutions` branch. That exercise branch is kept,
  frozen, as `exercises-archive` (its last commit, `906cbb0`, matches solutions commit
  `7dae398`); `master` is now the solution tree.

In the exercise tree an unimplemented exercise shows up in `lake test` as
`✗ ... not implemented yet (hit a sorry)`. The exercises of each stage are listed, in
order, in tables in the [stage docs](index.md) (numbered `1.1`, `2.4`, `12.2` …); work
through them in order, because later tests depend on earlier code.

## Markers

In `.lean` and `.wiz` files, a block

```
<indent>--<sol
...solution lines...
<indent>--|ex                (optional)
<indent>--| exercise line    (each line of the exercise version)
<indent>--sol>
```

becomes the exercise lines (with `--| ` stripped), or `<indent>sorry` when there is no
`--|ex` part. An empty `--|ex` part deletes the block (solution-only helpers). A
top-level block (no indentation) must have an `--|ex` part, possibly empty. Nested
blocks, stray markers and unterminated blocks are errors.

Files listed in `.solutions-only` are not copied to the exercise tree, and tracked files
of the exercise tree that no longer exist in the solution tree are deleted (when it is a
git worktree). `mkexercises.py` refuses to run on an exercise worktree with uncommitted
changes, and on a directory that is neither empty nor a git worktree.

When writing solutions, keep the exercise stubs runnable: the exercise tree must build,
and its test driver should run to its summary line. CI checks this only for a release:
the `exercise tree` job of `.github/workflows/release.yml` generates the tree and builds
it for each `v*` tag, and the release is published only if that passes. Between releases
the tree may stop building; fix it before tagging (generate it with `mkexercises.py` and
`lake build wiz grail tests` there).
