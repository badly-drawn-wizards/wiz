# scry

The code-analysis platform's grail package (S1 skeleton). The design is
`wiz-notes/code-analysis-design.md` §4/§6; the package layout, schema and the S1
checklist are in `wiz-notes/scry-package.md`.

There is **no tree-sitter yet**. `scry parse --stats` reads a hand-written JSON fact
store (`fixtures/demo.facts.json`), which exercises the schema, the loader, the CSR
adjacency and the CLI before the C shim exists.

```sh
cd scry
cp ../grail.local.wiz .         # this machine's toolchain (not committed)
grail build                     # check src, build .grail/bin/scry, run the 4 commands
grail test                      # the loader and CLI golden tests
grail run scry -- facts fixtures/demo.facts.json
grail run scry -- query fixtures/demo.facts.json --kind call_expression
grail run scry -- explain fixtures/demo.facts.json 4
grail run scry -- parse fixtures/demo.facts.json --stats
```

Commands: `facts`, `query --kind|--edge|--rel`, `explain`, `parse --stats`. The grail
targets `facts`, `query`, `explain` and `parse` install their output under `build/`
(ignored by git). S1 replaces the stub with `native/ts_shim.c`, a native column store
and schema codegen; see `wiz-notes/scry-package.md`.
