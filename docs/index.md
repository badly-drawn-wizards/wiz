# Wiz documentation

* [stability.md](stability.md): what a release promises (0.1.z)
* [release.md](release.md): making a release (checklist, tagging, smoke test)
* [CHANGELOG.md](../CHANGELOG.md)
* [building.md](building.md)
* [ci-runner.md](ci-runner.md): a self-hosted runner for the heavy CI shards
* [exercises.md](exercises.md): generating the exercise tree from this one
* [hardware.md](hardware.md): hardware in Wiz, from a circuit to a proved temporal property
* [CoreSpec.md](CoreSpec.md)
* [Status.md](Status.md)
* [resources.md](resources.md): resources in Wiz: quantities, regions, optics, Feral and separation logic, with one running example
* [ROADMAP.md](../ROADMAP.md)

## The stages

The implementation is built in stages; each stage's doc describes what it added, its
files, and its exercises. Section numbers (`4c`, `22e` …) are stable, and other docs and
comments refer to them: section `NNx` is in `stages/NN-*.md`. The stages are grouped by
topic below, so the numbers are not in order.

### The kernel and the elaborator (in Lean)

* [Stage 1: the core kernel](stages/01-kernel.md)
* [Stage 2: the extensible parser](stages/02-parser.md)
* [Stage 3: the elaborator](stages/03-elaborator.md)
* [Stage 4: data](stages/04-data.md)

### Running programs

* [Stage 5: erasure and the interpreter](stages/05-erasure.md)
* [Stage 6: macros](stages/06-macros.md)
* [Stage 7: type classes](stages/07-type-classes.md)
* [Stage 8: the backend](stages/08-backend.md)
* [Stage 9: the C FFI](stages/09-ffi.md)
* [Stage 10: effects](stages/10-effects.md)
* [Stage 25: concurrency](stages/25-concurrency.md)

### Self-hosting

* [Stage 12: towards self-hosting](stages/12-towards-selfhosting.md)
* [Stage 13: the language, for programs this size](stages/13-language.md)
* [Stage 14: the kernel in Wiz](stages/14-selfhost-kernel.md)
* [Stage 15: performance for self-hosting](stages/15-performance.md)
* [Stage 16: data in the self-hosted frontend](stages/16-selfhost-data.md)
* [Stage 17: elaboration in the self-hosted frontend](stages/17-selfhost-elaboration.md)
* [Stage 18: more data in the self-hosted frontend](stages/18-selfhost-more-data.md)
* [Stage 19: the frontend checks the self-hosted sources](stages/19-selfhost-checks-sources.md)
* [Stage 20: the frontend checks itself, and gets faster](stages/20-selfhost-checks-itself.md)
* [Stage 21: bootstrap](stages/21-bootstrap.md)

### Tooling

* [Stage 11: tooling](stages/11-tooling.md)
* [Stage 23: grail, a build tool](stages/23-grail.md)
* [Stage 26: tower, a toolchain manager](stages/26-tower.md)

### Numbers and libraries

* [Stage 22: numbers for hardware and systems code](stages/22-numbers.md)
* [Libraries](libraries.md)

### Verification

* [Stage 24: separation logic](stages/24-separation-logic.md)
