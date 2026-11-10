#!/bin/sh
# Check every hand-lowered program (and the runtime stand-ins) from the worktree root:
#   sh drafts/feral/check.sh
# The surface files (drafts/feral/surface) and drafts/feral/Optic.wiz are wishful: they
# don't check by design. The programs in drafts/feral/rejected are lowerings of programs
# Rust rejects: each must fail with a type error (or, for a forged handle, a
# private constructor).
set -e
WIZ=${WIZ:-./.lake/build/bin/wiz}
for f in drafts/feral/lib/FeralCore.wiz drafts/feral/lowered/*.wiz; do
  echo "== $f"
  "$WIZ" check --no-cache -I drafts/feral/lib "$f"
done
for f in drafts/feral/rejected/*.wiz; do
  echo "== $f (must be rejected)"
  if out=$("$WIZ" check --no-cache -I drafts/feral/lib "$f" 2>&1); then
    echo "accepted, but Rust rejects it: $f"; exit 1
  fi
  case "$out" in
    *"type mismatch"*|*"is private to module Region"*) echo "rejected: $(echo "$out" | head -1)" ;;
    *) echo "rejected for another reason:"; echo "$out"; exit 1 ;;
  esac
done
