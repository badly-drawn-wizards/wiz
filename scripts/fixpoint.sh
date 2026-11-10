#!/usr/bin/env bash
# The bootstrap fixpoint check. Stage 1, the self-hosted compiler built by the Lean
# `wiz build`, compiles the whole toolchain to C (self1.c); stage 2, that C compiled with
# selfhost/rt.c and Boehm GC, compiles the toolchain again (self2.c). They must be equal.
#   usage (from the repository root, in `nix develop`): scripts/fixpoint.sh [OUTDIR]
# Slow: two compilations of the whole toolchain (CI runs it on a schedule).
set -euo pipefail
out=${1:-.lake/fixpoint}
mkdir -p "$out/run"
out=$(cd "$out" && pwd)
: "${WIZ_GC_CFLAGS?needs the toolchain environment (nix develop)}"
step() { echo "::group::$1" 2>/dev/null; echo "== $1 ($(date +%T))"; }
done_() { echo "::endgroup::"; }

step "generate compiler.wiz and self.wiz"
lake build wiz Tests.Elab
OUT="$out" lake lean scripts/GenSelfhost.lean
cp "$out/self.wiz" "$out/run/input.wiz"
done_

step "stage 1: the Lean wiz build of the self-hosted compiler"
.lake/build/bin/wiz build "$out/compiler.wiz" -o "$out/compiler" --cflags "$WIZ_CFLAGS" --ldflags "$WIZ_LDFLAGS"
done_

step "stage 1 compiles the toolchain (self1.c)"
(cd "$out/run" && "$out/compiler" > "$out/self1.c")
done_

step "stage 2: cc self1.c with selfhost/rt.c"
# shellcheck disable=SC2086
cc -O2 -w -I"$PWD/selfhost" $WIZ_GC_CFLAGS "$out/self1.c" -o "$out/stage2" $WIZ_GC_LDFLAGS
done_

step "stage 2 compiles the toolchain (self2.c)"
(cd "$out/run" && "$out/stage2" > "$out/self2.c")
done_

if cmp -s "$out/self1.c" "$out/self2.c"; then
  echo "FIXPOINT (stage-1 C = stage-2 C, $(stat -c %s "$out/self1.c") bytes)"
else
  echo "NO FIXPOINT: $(cmp "$out/self1.c" "$out/self2.c" | head -1)"
  diff "$out/self1.c" "$out/self2.c" | head -40 || true
  exit 1
fi
