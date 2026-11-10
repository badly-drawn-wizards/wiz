/* The JavaScript side of web/Web.wiz's foreign functions, for Emscripten. Wiz marshals
   `String` as UTF-8 `char *`; `js_next_event` waits for the page (Asyncify suspends the
   whole Wiz program meanwhile), the others call into web/infoview.js. */
#include <emscripten.h>
#include <stdlib.h>

/* (An async import returns an int, not a pointer: with wasm64, Asyncify passes 0 for
   the result while it unwinds, which can't become an i64. The text comes back through
   `out`.) */
EM_ASYNC_JS(int, js_wait_event, (char **out), {
  const ev = await globalThis.wizNextEvent();
  setValue(Number(out), stringToNewUTF8(ev), "*");
  return 0;
});
static char *js_last = NULL;
/* The event's text stays valid until the next call (Wiz copies it at once). */
const char *js_next_event(void) {
  free(js_last);
  js_last = NULL;
  js_wait_event(&js_last);
  return js_last;
}
EM_JS(void, js_send, (const char *s), { globalThis.wizSend(UTF8ToString(Number(s))); });
EM_JS(void, js_set_html, (const char *id, const char *html), {
  globalThis.wizSetHtml(UTF8ToString(Number(id)), UTF8ToString(Number(html)));
});
