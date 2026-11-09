#!/bin/sh
# Build the terminal infoview: infoview/Tui.wiz with its C glue (infoview/term.c).
#   usage: infoview/build.sh [OUT]       (default .lake/build/bin/wiz-infoview)
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:-$ROOT/.lake/build/bin/wiz-infoview}
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
cd "$ROOT"
WIZ_LDFLAGS="$WIZ_LDFLAGS $ROOT/infoview/term.c" "$WIZ" build infoview/Tui.wiz -o "$OUT"
echo "built $OUT"
