// The browser half of the web infoview: a WebSocket to the language server
// (`wiz lsp --ws PORT`, which web/bridge.sh starts), the Wiz program compiled to WebAssembly (web/Web.wiz), and the page.
// Everything the infoview decides is in Wiz; this file only moves events in and HTML
// out. Every event is a step of the Wiz program (its export `wiz_web_step`, stage 9g),
// which calls back js_send and js_set_html (web/js.c).
"use strict";

const params = new URLSearchParams(location.search);
const port = params.get("port") || "8765";
// (one server serves every page, and documents are shared: a URI of our own)
const uri = params.get("uri") || `file:///scratch-${Math.random().toString(36).slice(2, 10)}.wiz`;

// Events for Wiz: each is a step `state = wiz_web_step(state, event)`. The state is a
// Wiz value (a reference the page owns, passed back in); the event's text is copied by
// Wiz. Events before the module is loaded wait in `early`.
let wasm = null;
let state = null;
const early = [];
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64
function step(ev) {
  const p = wasm.stringToNewUTF8(ev);
  state = wasm._wiz_web_step(state, big(p));
  wasm._free(p);
}
function post(kind, payload) {
  const ev = kind + "\n" + payload;
  if (wasm) step(ev); else early.push(ev);
}

// Messages to and from the server. Wiz frames its stream with Content-Length, as on
// stdio; the WebSocket carries one JSON-RPC message per text frame (protocol §8.2), so
// outgoing frames are cut out of the stream here, and incoming ones get their header.
let sock = null;
const outbox = [];
const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8");
let pending = new Uint8Array(0);   // bytes from Wiz not yet a whole message
function sendMessage(text) {
  if (sock && sock.readyState === WebSocket.OPEN) sock.send(text); else outbox.push(text);
}
globalThis.wizSend = (text) => {
  const more = encoder.encode(text);
  const buf = new Uint8Array(pending.length + more.length);
  buf.set(pending); buf.set(more, pending.length);
  let at = 0;
  for (;;) {
    let end = -1;   // the blank line after the headers
    for (let i = at; i + 3 < buf.length; i++)
      if (buf[i] === 13 && buf[i + 1] === 10 && buf[i + 2] === 13 && buf[i + 3] === 10) { end = i; break; }
    if (end < 0) break;
    const m = /Content-Length:\s*(\d+)/i.exec(decoder.decode(buf.subarray(at, end)));
    const len = m ? Number(m[1]) : 0;
    if (end + 4 + len > buf.length) break;
    sendMessage(decoder.decode(buf.subarray(end + 4, end + 4 + len)));
    at = end + 4 + len;
  }
  pending = buf.slice(at);
};
function received(text) {
  post("net", `Content-Length: ${encoder.encode(text).length}\r\n\r\n${text}`);
}
globalThis.wizSetHtml = (id, html) => {
  const el = document.getElementById(id);
  if (el) el.innerHTML = html;
};

function setStatus(text) { document.getElementById("status").textContent = text; }

function connect() {
  sock = new WebSocket(`ws://127.0.0.1:${port}/`);
  sock.onopen = () => {
    setStatus("connected");
    for (const b of outbox.splice(0)) sock.send(b);
  };
  sock.onmessage = (m) => received(m.data);
  sock.onclose = () => setStatus("disconnected (is `wiz lsp --ws` running?)");
  sock.onerror = () => setStatus("cannot connect to ws://127.0.0.1:" + port);
}

// The editor: a textarea. Its cursor as an LSP position (0-based, in characters).
const editor = document.getElementById("editor");
function cursor() {
  const before = Array.from(editor.value.slice(0, editor.selectionStart));
  let line = 0, col = 0;
  for (const c of before) { if (c === "\n") { line++; col = 0; } else col++; }
  return [line, col];
}
let lastPos = "";
let opened = false;   // (cursor moves before the document is open would ask about nothing)
function onCursor() {
  if (!opened) return;
  const [l, c] = cursor();
  const key = l + " " + c;
  if (key === lastPos) return;
  lastPos = key;
  document.getElementById("pos").textContent = `${l + 1}:${c + 1}`;
  post("cursor", key);
}
let changeTimer = null;
editor.addEventListener("input", () => {
  clearTimeout(changeTimer);
  changeTimer = setTimeout(() => { if (!opened) return; post("change", editor.value); lastPos = ""; onCursor(); }, 300);
});
for (const ev of ["keyup", "click", "select"]) editor.addEventListener(ev, onCursor);

// The infoview: clicks select a subterm (event delegation: one listener for every
// tag Wiz renders), the innermost tag under the mouse is highlighted, arrows navigate.
const goals = document.getElementById("goals");
goals.addEventListener("click", (e) => {
  const t = e.target.closest(".tt");
  if (t) post("click", t.dataset.idx);
});
goals.addEventListener("mouseover", (e) => {
  for (const h of goals.querySelectorAll(".hover")) h.classList.remove("hover");
  const t = e.target.closest(".tt");
  if (t) t.classList.add("hover");
});
goals.addEventListener("keydown", (e) => {
  if (["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Escape"].includes(e.key)) {
    e.preventDefault();
    post("key", e.key);
  }
});

// Start: load the Wasm module (Emscripten's loader, web/build.sh), open the document.
async function start() {
  setStatus("loading");
  const createModule = (await import("./wiz-infoview.mjs")).default;
  wasm = await createModule({ print: (s) => console.log(s), printErr: (s) => console.warn(s) });
  state = wasm._wiz_web_init();
  for (const ev of early.splice(0)) step(ev);
  connect();
  post("open", uri + "\n" + editor.value);
  opened = true;
  onCursor();
}
start().catch((e) => setStatus("failed: " + e));
