#!/usr/bin/env bash
# Checks that Lake tracks runtime/wiz.c, which runtime/WizRuntime.lean embeds with
# include_str (docs/building.md, "Embedded files"). In a temporary copy of the checkout:
#
# 1. build; with no edit, WizRuntime and Wiz.Compiler.C are up to date (`--no-build`);
# 2. add a fresh comment to wiz.c: now they are out of date, but a module that doesn't
#    import the runtime (Wiz.Compiler.IR) is not; rebuild (through Lake's artifact cache,
#    which must not serve the old module) and check the new text is embedded;
# 3. undo the edit: the original text is embedded again.
#
# Usage: scripts/test-embed.sh (from anywhere; run it through `heavy`)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-test-embed.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
# the checkout's files, with uncommitted changes (not .lake: the copy builds from the cache)
(cd "$root" && git ls-files -co --exclude-standard -z | xargs -0 cp --parents -t "$tmp")
cd "$tmp"

mods=(WizRuntime Wiz.Compiler.C)
marker="test-embed marker $$-$(date +%s%N)"
fail() { echo "test-embed: FAIL: $*"; exit 1; }
embedded() { # does the built WizRuntime embed $1? (anything but true/false is an error)
  printf 'import WizRuntime\n#eval IO.println (if (Wiz.C.runtime.splitOn "%s").length > 1 then "true" else "false")\n' "$1" > Probe.lean
  local out; out=$(lake lean Probe.lean 2>&1) || fail "the probe failed: $out"
  case "$out" in true) return 0 ;; false) return 1 ;; *) fail "the probe printed: $out" ;; esac
}

lake build -q "${mods[@]}"
lake build --no-build "${mods[@]}" >/dev/null || fail "no edit, but the modules are out of date"
embedded "$marker" && fail "the marker is embedded before the edit"
echo "ok: no edit, nothing to rebuild"

cp runtime/wiz.c "$tmp/wiz.c.orig"
printf '/* %s */\n' "$marker" >> runtime/wiz.c
for m in "${mods[@]}"; do
  lake build --no-build "$m" >/dev/null 2>&1 && fail "wiz.c changed but $m is up to date"
done
lake build --no-build Wiz.Compiler.IR >/dev/null || fail "wiz.c changed and Wiz.Compiler.IR is out of date"
echo "ok: editing wiz.c makes WizRuntime and Wiz.Compiler.C (only) out of date"
lake build -q "${mods[@]}"
embedded "$marker" || fail "rebuilt, but the new wiz.c is not embedded"
lake build --no-build "${mods[@]}" >/dev/null || fail "rebuilt, but still out of date"
echo "ok: rebuilt, and the new text is embedded"

cp "$tmp/wiz.c.orig" runtime/wiz.c
lake build -q "${mods[@]}"
embedded "$marker" && fail "the edit was undone, but the marker is still embedded"
echo "ok: undone, the original text is embedded again"
echo "test-embed: all checks passed"
