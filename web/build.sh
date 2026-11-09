#!/bin/sh
# Build the web infoview: web/Web.wiz → C (the Wiz compiler) → WebAssembly (Emscripten),
# with the reference-counting runtime and mini-gmp (GMP's portable subset) for bignums.
#   usage: web/build.sh [OUT]       (default web/out; needs .lake/build/bin/wiz)
# wasm64 (-sMEMORY64) keeps the runtime's 64-bit words and 62-bit small numbers as they
# are; Asyncify lets `js_next_event` wait for the page without callbacks into Wiz.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mkdir -p "${1:-$ROOT/web/out}" && cd "${1:-$ROOT/web/out}" && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
if command -v emcc >/dev/null; then EMCC=emcc; else EMCC="nix shell nixpkgs#emscripten -c emcc"; fi

# 1. Wiz → C: `wiz build` writes OUT/web.c, then runs $WIZ_CC, here a no-op.
(cd "$ROOT" && WIZ_CC=true "$WIZ" build web/Web.wiz -o "$OUT/web")

# 2. mini-gmp from GMP's source tarball, behind a <gmp.h>
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=$(nix build --no-link --print-out-paths nixpkgs#gmp.src)
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi

# 3. C → wasm, as an ES module that web/infoview.js imports
$EMCC -O2 -w -I"$OUT/gmp" "$OUT/web.c" "$OUT/gmp/mini-gmp.c" "$ROOT/web/js.c" \
  -sMEMORY64=1 -sASYNCIFY -sASYNCIFY_STACK_SIZE=4194304 -sSTACK_SIZE=33554432 \
  -sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
  '-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=$setValue,$stringToNewUTF8,$UTF8ToString' \
  -o "$OUT/wiz-infoview.mjs"
cp "$ROOT/web/infoview.html" "$ROOT/web/infoview.js" "$OUT/"
echo "built $OUT/wiz-infoview.mjs"
