#!/bin/sh
# Tests of the terminal infoview: against infoview/stub_server.py (the socket protocol of
# infoview-protocol.md §8, with canned goals) once with --dump (plain text) and once
# interactively in a pseudo-terminal (select a subterm, ask what it is, quit); then end
# to end, against the real `wiz lsp --infoview SOCK` with infoview/editor_stub.py as the
# editor.
#   usage: infoview/test.sh [BINARY]     (default: build one in a temporary directory)
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
BIN=${1:-$TMP/wiz-infoview}
[ -n "$1" ] || "$ROOT/infoview/build.sh" "$BIN" >/dev/null
check() {   # name expected-file actual-file
  if diff -u "$2" "$3"; then echo "ok: $1"; else echo "FAIL: $1"; exit 1; fi
}
stub() {
  python3 "$ROOT/infoview/stub_server.py" "$TMP/s.sock" --once &
  i=0; while [ ! -S "$TMP/s.sock" ] && [ $i -lt 50 ]; do sleep 0.1; i=$((i+1)); done
}

stub
"$BIN" "$TMP/s.sock" --dump --width 24 > "$TMP/dump.txt"
cat > "$TMP/dump.exp" <<'END'
Tactic state
A : Type
x : A
⊢ Nat → A
END
check "dump" "$TMP/dump.exp" "$TMP/dump.txt"
wait

stub
python3 "$ROOT/infoview/pty_test.py" 40 8 '\x1b[C|\x1b[C|\x1b[C|\x1b[C|q' -- "$BIN" "$TMP/s.sock" > "$TMP/screen.txt"
wait
sed -n '2,5p;8p' "$TMP/screen.txt" > "$TMP/screen.cut"
cat > "$TMP/screen.exp" <<'END'
Tactic state
A : Type
x : A
⊢ Nat → A
[const] Nat : Type
END
check "interactive: select the fourth subterm, Nat" "$TMP/screen.exp" "$TMP/screen.cut"

cat > "$TMP/t.wiz" <<'END'
import Prelude
def k : (A : Type) → A → Nat → A := by
  intro A
  intro x
  intro n
  exact x
END
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
(cd "$ROOT" && python3 "$ROOT/infoview/editor_stub.py" "$WIZ" "$TMP/lsp.sock" "$TMP/t.wiz" 3 9 -- \
  "$BIN" "$TMP/lsp.sock" --dump --width 40) > "$TMP/e2e.txt"
cat > "$TMP/e2e.exp" <<'END'
Tactic state
A : Type
x : A
⊢ Nat → A
END
head -4 "$TMP/e2e.txt" > "$TMP/e2e.cut"
check "end to end: wiz lsp --infoview, the goals after intro x" "$TMP/e2e.exp" "$TMP/e2e.cut"
