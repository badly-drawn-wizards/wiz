#!/bin/sh
# Smoke test of the web infoview, headless: build the page (web/build.sh), serve it with
# web/bridge.sh in front of infoview/stub_server.py (canned goals), load it in headless
# Chromium and look for the goals in the DOM, rendered by the Wasm build of web/Web.wiz.
#   usage: web/test.sh [PORT]       (needs nix for emscripten, websocat, chromium)
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PORT=${1:-18765}
OUT=$(mktemp -d)
trap 'pkill -P $BRIDGE 2>/dev/null; kill $BRIDGE 2>/dev/null; rm -rf "$OUT"' EXIT
"$ROOT/web/build.sh" "$OUT" >/dev/null
WIZ_WEB_OUT=$OUT "$ROOT/web/bridge.sh" "$PORT" "python3 $ROOT/infoview/stub_server.py --stdio" > "$OUT/bridge.log" 2>&1 &
BRIDGE=$!
sleep 3
if command -v chromium >/dev/null; then CHROME=chromium; else CHROME="nix shell nixpkgs#chromium -c chromium"; fi
$CHROME --headless --no-sandbox --disable-gpu --virtual-time-budget=8000 --run-all-compositor-stages-before-draw \
  --dump-dom "http://127.0.0.1:$((PORT + 1))/infoview.html?port=$PORT" 2>/dev/null > "$OUT/dom.html"
ok=1
for want in 'id="status">connected' 'class="names">A</span>' 'data-ref="5"' '<span class="turnstile">⊢</span>'; do
  if grep -qF "$want" "$OUT/dom.html"; then echo "ok: $want"; else echo "FAIL: missing $want"; ok=0; fi
done
[ $ok = 1 ] || { sed -n '/<body>/,/<\/body>/p' "$OUT/dom.html" | head -40; exit 1; }
