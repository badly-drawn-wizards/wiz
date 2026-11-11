/* The JavaScript side of web/Web.wiz's foreign functions, for Emscripten. Wiz marshals
   `String` as UTF-8 `char *`; both call into web/infoview.js. (Events go the other way,
   into the exported `wiz_web_step`.) */
#include <emscripten.h>

EM_JS(void, js_send, (const char *s), { globalThis.wizSend(UTF8ToString(Number(s))); });
EM_JS(void, js_set_html, (const char *id, const char *html), {
  globalThis.wizSetHtml(UTF8ToString(Number(id)), UTF8ToString(Number(html)));
});
