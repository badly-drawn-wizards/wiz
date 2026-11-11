#!/bin/sh
# Build the terminal infoview: infoview/Tui.wiz (with its C glue infoview/term.c, by link_c).
#   usage: infoview/build.sh [OUT]       (default .lake/build/bin/wiz-infoview)
# GMP's flags come from $WIZ_CFLAGS and $WIZ_LDFLAGS (as /workspace/wiz-env.sh sets them),
# passed on to wiz as --cflags/--ldflags.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:-$ROOT/.lake/build/bin/wiz-infoview}
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
cd "$ROOT"
# (infoview/term.c comes with it: Tui.wiz says `link_c "term.c"`)
"$WIZ" --cflags "$WIZ_CFLAGS" --ldflags "$WIZ_LDFLAGS" build infoview/Tui.wiz -o "$OUT"
echo "built $OUT"
