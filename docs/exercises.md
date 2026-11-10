# Exercises and solutions

Wiz is also a course: each stage leaves parts of the implementation as exercises, and the
test suite tells you when you've got them right. The repository keeps one tree with the
solutions in it, and generates the exercise tree from it.

## The two trees

* **The solution tree** (the `solutions` branch) is the complete implementation. Every
  exercise is a marked block whose solution and exercise versions sit side by side.
* **The exercise tree** (the `master` branch) is generated from it by
  `scripts/mkexercises.py SRC_WORKTREE DST_WORKTREE`: each marked block is replaced by
  its exercise version. Nobody edits it by hand; it is regenerated after every merge into
  the solution tree.

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
of the exercise tree that no longer exist in the solution tree are deleted.
`mkexercises.py` refuses to run on an exercise worktree with uncommitted changes.

When writing solutions, keep the exercise stubs runnable: the exercise tree must build,
and its test driver must run to its summary line (CI checks both; see
[building.md](building.md)).
