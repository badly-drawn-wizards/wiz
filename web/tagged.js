// The browser half that the web infoview (web/infoview.js) and the documentation's
// pages (web/scroll.js, `wiz doc`) share: loading the Wasm module (web/Web.wiz, built by
// web/build.sh), stepping it with events, and the mouse and keys on tagged text
// (`<span class="tt" data-idx>`, lib/Tagged.wiz's HTML). What to do with an event is
// decided in Wiz; this only moves events in.
"use strict";

export const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// The module (Emscripten's loader), next to the page.
export async function loadWasm(url = "./wiz-infoview.mjs") {
  const createModule = (await import(url)).default;
  return createModule({ print: (s) => console.log(s), printErr: (s) => console.warn(s) });
}

// A Wiz program stepped by events: `state = step(state, event)` (stage 9g). The state is
// a Wiz value the page holds; the event's text is copied by Wiz.
export function stepper(wasm, init, step) {
  let state = wasm[init]();
  return (ev) => {
    const p = wasm.stringToNewUTF8(ev);
    state = wasm[step](state, big(p));
    wasm._free(p);
  };
}

// Tagged text under `root`: the innermost tag under the mouse is highlighted (and
// `hover(tag)` called), `click(tag)` on a click, `key(name)` for the arrows and Escape
// (the default action prevented), `leave()` when the mouse leaves every tag.
export function delegate(root, { click, hover, leave, key } = {}) {
  let last = null;
  root.addEventListener("mouseover", (e) => {
    const t = e.target.closest(".tt");
    if (t === last) return;
    for (const h of root.querySelectorAll(".tt.hover")) h.classList.remove("hover");
    last = t;
    if (t) { t.classList.add("hover"); if (hover) hover(t); }
    else if (leave) leave();
  });
  root.addEventListener("mouseleave", () => {
    for (const h of root.querySelectorAll(".tt.hover")) h.classList.remove("hover");
    last = null;
    if (leave) leave();
  });
  root.addEventListener("click", (e) => {
    const t = e.target.closest(".tt");
    if (t && click) { e.preventDefault(); click(t); }
  });
  root.addEventListener("keydown", (e) => {
    if (key && ["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Escape"].includes(e.key)) {
      e.preventDefault();
      key(e.key);
    }
  });
}
