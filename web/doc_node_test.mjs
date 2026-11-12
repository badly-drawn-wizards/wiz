// (11s) The documentation page's half of the Wasm module under Node: web/scroll.js's
// hooks and nothing else. Hands it the first declaration of a page's JSON (`wiz doc`'s
// A.B.json), hovers and clicks tag 1, and prints what it set.
//   usage: node web/doc_node_test.mjs OUT_DIR PAGE.json
import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";
const [outDir, page] = process.argv.slice(2);
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));
globalThis.wizSetHtml = (id, h) => console.log(`${id}: ${h}`);
globalThis.wizGo = (u) => console.log(`go: ${u}`);
const createModule = (await import(pathToFileURL(outDir + "/wiz-infoview.mjs").href)).default;
const wasm = await createModule({ printErr: (s) => console.error(s) });
let state = wasm._wiz_doc_init();
const post = (ev) => {
  const p = wasm.stringToNewUTF8(ev);
  state = wasm._wiz_doc_step(state, big(p));
  wasm._free(p);
};
const decl = JSON.parse(readFileSync(page, "utf-8")).decls[0];
post("decl\n" + JSON.stringify(decl));
post(`hover\n${decl.id} 1`);
post(`click\n${decl.id} 1`);
post(`click\n${decl.id} 0`);
