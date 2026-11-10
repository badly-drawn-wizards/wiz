// The web infoview's Wasm module under Node, with a language server as a child process
// in place of the WebSocket: web/infoview.js's three hooks, nothing else. Prints the
// HTML Wiz sets, after opening a document, moving the cursor and clicking subterm 3.
//   usage: node web/node_test.mjs OUT_DIR SERVER_CMD...
import { spawn } from "node:child_process";
import { pathToFileURL } from "node:url";
const [outDir, ...server] = process.argv.slice(2);
const events = [];
let waiting = null;
const post = (kind, payload) => {
  const ev = kind + "\n" + payload;
  if (waiting) { const w = waiting; waiting = null; w(ev); } else events.push(ev);
};
globalThis.wizNextEvent = () =>
  events.length ? Promise.resolve(events.shift()) : new Promise((r) => { waiting = r; });
const lsp = spawn(server[0], server.slice(1), { stdio: ["pipe", "pipe", "inherit"] });
const decoder = new TextDecoder("utf-8");
lsp.stdout.on("data", (b) => post("net", decoder.decode(b, { stream: true })));
globalThis.wizSend = (text) => lsp.stdin.write(text);
const html = {};
globalThis.wizSetHtml = (id, h) => { html[id] = h; };
const createModule = (await import(pathToFileURL(outDir + "/wiz-infoview.mjs").href)).default;
await createModule({ printErr: (s) => console.error(s) });
post("open", "file:///t.wiz\nimport Prelude\n");
post("cursor", "3 4");
setTimeout(() => post("click", "3"), 1500);
setTimeout(() => {
  console.log("goals: " + (html.goals || ""));
  console.log("info: " + (html.info || ""));
  lsp.kill();
  process.exit(0);
}, 3000);
