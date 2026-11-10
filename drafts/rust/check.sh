#!/bin/sh
# Check every hand-lowered program (and the runtime stand-ins) from the worktree root:
#   sh drafts/rust/check.sh
# The surface files (drafts/rust/surface) and drafts/rust/Optic.wiz are wishful: they
# don't check by design.
set -e
WIZ=${WIZ:-./.lake/build/bin/wiz}
for f in drafts/rust/lib/RsCore.wiz drafts/rust/lowered/*.wiz; do
  echo "== $f"
  "$WIZ" check --no-cache -I drafts/rust/lib "$f"
done
