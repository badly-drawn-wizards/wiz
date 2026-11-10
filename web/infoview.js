// The browser half of the web infoview: a WebSocket to the language server (through
// web/bridge.sh), the Wiz program compiled to WebAssembly (web/Web.wiz), and the page.
// Everything the infoview decides is in Wiz; this file only moves events in and HTML
// out. The Wiz side calls js_next_event (async: Asyncify suspends it), js_send and
// js_set_html (web/js.c).
"use strict";

const params = new URLSearchParams(location.search);
const port = params.get("port") || "8765";
const uri = params.get("uri") || "file:///scratch.wiz";

// Events for Wiz, and the one waiting `js_next_event`, if any.
const events = [];
let waiting = null;
function post(kind, payload) {
  const ev = kind + "\n" + payload;
  if (waiting) { const w = waiting; waiting = null; w(ev); } else events.push(ev);
}
globalThis.wizNextEvent = () =>
  events.length ? Promise.resolve(events.shift()) : new Promise((r) => { waiting = r; });

// Bytes to and from the server: one stream, framed by Wiz (Content-Length).
let sock = null;
const outbox = [];
const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8");   // with {stream: true}: a character cut in two waits
globalThis.wizSend = (text) => {
  const bytes = encoder.encode(text);
  if (sock && sock.readyState === WebSocket.OPEN) sock.send(bytes); else outbox.push(bytes);
};
globalThis.wizSetHtml = (id, html) => {
  const el = document.getElementById(id);
  if (el) el.innerHTML = html;
};

function setStatus(text) { document.getElementById("status").textContent = text; }

function connect() {
  sock = new WebSocket(`ws://127.0.0.1:${port}/`);
  sock.binaryType = "arraybuffer";
  sock.onopen = () => {
    setStatus("connected");
    for (const b of outbox.splice(0)) sock.send(b);
  };
  sock.onmessage = (m) => {
    const text = typeof m.data === "string" ? m.data : decoder.decode(m.data, { stream: true });
    if (text) post("net", text);
  };
  sock.onclose = () => setStatus("disconnected (is web/bridge.sh running?)");
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
function onCursor() {
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
  changeTimer = setTimeout(() => { post("change", editor.value); lastPos = ""; onCursor(); }, 300);
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
  createModule({ print: (s) => console.log(s), printErr: (s) => console.warn(s) });
  connect();
  post("open", uri + "\n" + editor.value);
  onCursor();
}
start().catch((e) => setStatus("failed: " + e));
