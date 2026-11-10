#!/bin/sh
# The web infoview's bridge: a WebSocket on 127.0.0.1:PORT in front of `wiz lsp` (one
# server per connection), and the page itself over HTTP on PORT+1. Bytes pass through
# unchanged (`-b`); the page frames JSON-RPC itself. Stands in for `wiz lsp --ws PORT`.
#   usage: web/bridge.sh [PORT] [WIZ]      then open http://127.0.0.1:PORT+1/infoview.html
set -e
PORT=${1:-8765}
WIZ=${2:-wiz}
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${WIZ_WEB_OUT:-$HERE/out}
[ -f "$OUT/wiz-infoview.mjs" ] || { echo "build the page first: web/build.sh" >&2; exit 1; }
cp "$HERE/infoview.html" "$HERE/infoview.js" "$OUT/"
if command -v websocat >/dev/null; then WS=websocat; else WS="nix shell nixpkgs#websocat -c websocat"; fi
python3 -m http.server --bind 127.0.0.1 --directory "$OUT" $((PORT + 1)) >/dev/null 2>&1 &
HTTP=$!
trap 'kill $HTTP 2>/dev/null' EXIT INT TERM
echo "infoview: http://127.0.0.1:$((PORT + 1))/infoview.html?port=$PORT"
$WS -b ws-l:127.0.0.1:$PORT cmd:"$WIZ lsp"
