// Drive headless Chromium over the DevTools protocol (Node's built-in WebSocket): open
// the page, wait (in real time) until the infoview shows the goals, click a subterm, and
// print the goals' and info's HTML, the status line and any console errors.
//   usage: node web/chrome_test.mjs CHROMIUM URL
import { spawn } from "node:child_process";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
const [chrome, url] = process.argv.slice(2);
const port = 9300 + Math.floor(Math.random() * 500);
const profile = mkdtempSync(join(tmpdir(), "wiz-chrome-"));
const proc = spawn(chrome, ["--headless", "--no-sandbox", "--disable-gpu", `--remote-debugging-port=${port}`,
  `--user-data-dir=${profile}`, "about:blank"], { stdio: "ignore" });
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const done = (code) => { proc.kill(); process.exit(code); };
setTimeout(() => { console.log("timeout"); done(1); }, 60000);
let target = null;
for (let i = 0; i < 100 && !target; i++) {
  await sleep(200);
  try { target = (await (await fetch(`http://127.0.0.1:${port}/json/list`)).json()).find((t) => t.type === "page"); } catch {}
}
const ws = new WebSocket(target.webSocketDebuggerUrl);
await new Promise((r) => ws.addEventListener("open", r));
let id = 0;
const pending = new Map();
const errors = [];
ws.addEventListener("message", (m) => {
  const msg = JSON.parse(m.data);
  if (msg.id && pending.has(msg.id)) { pending.get(msg.id)(msg.result); pending.delete(msg.id); }
  if (msg.method === "Runtime.exceptionThrown") errors.push(msg.params.exceptionDetails.exception?.description);
  if (msg.method === "Runtime.consoleAPICalled" && msg.params.type === "error")
    errors.push(msg.params.args.map((a) => a.value).join(" "));
});
const call = (method, params = {}) => new Promise((r) => { pending.set(++id, r); ws.send(JSON.stringify({ id, method, params })); });
const evaluate = async (expr) => (await call("Runtime.evaluate", { expression: expr, returnByValue: true })).result.value;
await call("Runtime.enable");
await call("Page.navigate", { url });
const has = (sel) => evaluate(`!!document.querySelector(${JSON.stringify(sel)})`);
for (let i = 0; i < 100 && !(await has("#goals .tt")); i++) await sleep(200);
await evaluate(`document.querySelectorAll("#goals .tt")[3]?.click()`);
for (let i = 0; i < 50 && !(await has("#info .kind")); i++) await sleep(200);
console.log("status: " + await evaluate(`document.getElementById("status").textContent`));
console.log("goals: " + await evaluate(`document.getElementById("goals").innerHTML`));
console.log("info: " + await evaluate(`document.getElementById("info").innerHTML`));
for (const e of errors) console.log("error: " + e);
done(0);
