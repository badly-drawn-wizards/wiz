#!/bin/sh
# Smoke tests of the web infoview: build the page (web/build.sh); run its Wasm module
# under Node with infoview/stub_server.py (canned goals) as the server
# (web/node_test.mjs); then serve it with web/bridge.sh in front of the real server
# (`wiz lsp --ws`, .lake/build/bin/wiz), load it in headless Chromium
# (web/chrome_test.mjs, over the DevTools protocol), put the cursor in the page's proof,
# click a subterm and look for the goals and what the subterm is in the DOM.
#   usage: web/test.sh [PORT]       (needs nix for emscripten and chromium)
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PORT=${1:-18765}
OUT=$(mktemp -d)
trap 'pkill -P $BRIDGE 2>/dev/null; kill $BRIDGE 2>/dev/null; rm -rf "$OUT"' EXIT
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
"$ROOT/web/build.sh" "$OUT" >/dev/null
node "$ROOT/web/node_test.mjs" "$OUT" python3 "$ROOT/infoview/stub_server.py" --stdio > "$OUT/node.txt"
for want in 'class="names">A</span>' 'data-ref="5"' 'info: <span class="kind">const</span> <code>Nat : Type</code>'; do
  if grep -qF "$want" "$OUT/node.txt"; then echo "ok (node): $want"; else echo "FAIL (node): missing $want"; cat "$OUT/node.txt"; exit 1; fi
done
# (11s) the documentation pages' half of the module, on a page `wiz doc` made
mkdir -p "$OUT/doc/src"
printf 'import Prelude\n/-- A colour. -/\ninductive C where\n  | red\n/-- The colour. -/\ndef pick (n : Nat) : C := C.red\n' > "$OUT/doc/src/Col.wiz"
"$WIZ" doc "$OUT/doc/src" -o "$OUT/doc/site" --web "$OUT" >/dev/null
python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); d["decls"]=[x for x in d["decls"] if x["name"]=="pick"]; json.dump(d,open(sys.argv[1],"w"))' "$OUT/doc/site/Col.json"
node "$ROOT/web/doc_node_test.mjs" "$OUT" "$OUT/doc/site/Col.json" > "$OUT/doc.txt"
for want in 'class="tt k-const" data-ref=' 'info: <span class="kind">const</span> <code>Nat : Type</code>' 'tt k-pi sel'; do
  if grep -qF "$want" "$OUT/doc.txt"; then echo "ok (doc, node): $want"; else echo "FAIL (doc, node): missing $want"; cat "$OUT/doc.txt"; exit 1; fi
done
[ -n "$WIZ_WEB_NO_BROWSER" ] && exit 0
WIZ_WEB_OUT=$OUT "$ROOT/web/bridge.sh" "$PORT" "$WIZ" > "$OUT/bridge.log" 2>&1 &
BRIDGE=$!
sleep 3
if command -v chromium >/dev/null; then CHROME=$(command -v chromium); else CHROME=$(nix shell nixpkgs#chromium -c sh -c 'command -v chromium'); fi
node "$ROOT/web/chrome_test.mjs" "$CHROME" "http://127.0.0.1:$((PORT + 1))/infoview.html?port=$PORT" > "$OUT/chrome.txt"
ok=1
for want in 'status: connected' 'class="names">A</span>' 'data-ref="' 'tt k-const sel' 'info: <span class="kind">const</span> <code>Nat : Type</code>'; do
  if grep -qF "$want" "$OUT/chrome.txt"; then echo "ok (chromium): $want"; else echo "FAIL (chromium): missing $want"; ok=0; fi
done
[ $ok = 1 ] || { cat "$OUT/chrome.txt" "$OUT/bridge.log"; exit 1; }
