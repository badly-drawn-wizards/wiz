# wiz

Wiz is a dependently typed language with quantitative types, built in Lean 4 as a
learning project and meant as the basis of a course in the style of *Software
Foundations*: each stage of the implementation is a set of exercises, with a test suite
that tells you when you've got them right. The toolchain is self-hosted: its kernel,
elaborator and compiler are also written in Wiz.

```
def id {0 A : Type} (1 x : A) : A := x
```

## Features

* **Quantitative type theory**: quantities `0`, `1`, `ω` on binders (the kernel is
  parametric in the rig), and quantity polymorphism; erased arguments cost nothing at
  run time.
* **Observational equality** with an impredicative, proof-irrelevant `Prop`: function
  extensionality, and `cast` that computes on data.
* **Data as descriptions**: `inductive` and `structure` elaborate to indexed
  descriptions with `μ`/`ν`; dependent pattern matching, mutual and indexed families.
* **Sized types** for termination and productivity, and **codata** (`ν`, copatterns).
* **Self-hosted**: the kernel, frontend and compiler in `selfhost/*.wiz` check and
  compile themselves, and the bootstrap reaches a fixpoint (stage-1 C = stage-2 C).
* **Native code**: erasure to an IR with Perceus reference counting and reuse, C and
  LLVM backends, a C FFI with header import, and machine integers and bit vectors.
* **Tooling**: a language server with an infoview (terminal and browser clients),
  a content-addressed elaboration cache, and **grail**, a build tool and test runner
  configured in Wiz.
* **Nix**: `nix develop` gives the whole toolchain; prebuilt binaries are on Cachix.

## Quick start

Run Wiz without a checkout, with the binaries from the public Cachix cache:

<!-- TODO: drop `/solutions` from the URL when solutions becomes the default branch (master). -->
```sh
cachix use badlydrawnwizards
nix run github:badly-drawn-wizards/wiz/solutions#wiz -- check hello.wiz   # `#grail` for grail
```

Or install toolchains with **tower** (like elan/rustup: `wiz` and `grail` shims on
`PATH`, a `wiz-toolchain` file per project; [docs/stages/26-tower.md](docs/stages/26-tower.md)):

```sh
nix profile install github:badly-drawn-wizards/wiz#tower
tower --self ~/.nix-profile/bin/tower self install   # shims in ~/.tower/bin: put it on PATH
tower default nightly
```

From a checkout:

```sh
nix develop         # the toolchain; writes this machine's paths to grail.local.wiz
lake build          # the library and the `wiz` executable
lake test           # the test suite (`lake test -- --list` for the groups)
```

See [docs/building.md](docs/building.md) for the details, CI and caches.

## Documentation

* [docs/index.md](docs/index.md): the stage-by-stage docs, one file per stage.
* [docs/CoreSpec.md](docs/CoreSpec.md): the kernel's calculus as inference rules.
* [docs/Status.md](docs/Status.md): what is proved, what is conjectured, and the known
  soundness issues. Nothing about Wiz as a whole is proved yet.
* [ROADMAP.md](ROADMAP.md): the plan and the design decisions behind it.

**Exercises.** Exercises are marked blocks in the solution tree;
`scripts/mkexercises.py` generates the exercise tree, with `sorry` stubs, from it (see
[docs/exercises.md](docs/exercises.md)).
