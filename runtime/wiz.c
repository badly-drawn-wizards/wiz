/* The Wiz runtime (stage 8b), included at the top of every generated C file.

   A value is a machine word. If its lowest bit is 1 it is a **scalar** (a small
   number, a tag, or ◾) holding `v >> 1`; otherwise it points to an **object**: a
   header (reference count, tag, number of fields) and the fields. Closures and big
   numbers (GMP) are objects with reserved tags. Reference counts follow the IR's
   `dup`/`drop` (Perceus): every function owns its arguments. */

#include <alloca.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>

typedef uintptr_t wiz_val;

/* Generated C includes this file, so everything is `static`. For the LLVM backend it
   is compiled on its own with -DWIZ_API= so the functions are exported. */
#ifndef WIZ_API
#define WIZ_API static
#endif

#define WIZ_BOX(n) ((((wiz_val)(n)) << 1) | 1)
#define WIZ_UNBOX(v) ((v) >> 1)
#define WIZ_IS_SCALAR(v) ((v) & 1)
#define WIZ_MAX_SMALL (((uintptr_t)1 << 62) - 1)

enum { WIZ_TAG_CLO = 0xFFFF0000u, WIZ_TAG_BIG = 0xFFFF0001u, WIZ_TAG_RAW = 0xFFFF0002u };

typedef struct {
  int64_t rc;
  uint32_t tag;
  uint32_t size;
} wiz_hdr;

typedef wiz_val (*wiz_boxed_fn)(wiz_val *);

typedef struct {
  wiz_hdr h;
  wiz_val fields[];
} wiz_ctor;

typedef struct {
  wiz_hdr h; /* size = number of captured arguments */
  wiz_boxed_fn fn;
  uint32_t arity;
  wiz_val args[];
} wiz_clo;

typedef struct {
  wiz_hdr h;
  mpz_t z;
} wiz_big;

static int64_t wiz_live = 0;

static void wiz_panic(const char *msg) {
  fprintf(stderr, "wiz: %s\n", msg);
  exit(3);
}

static void *wiz_alloc(size_t bytes, uint32_t tag, uint32_t size) {
  wiz_hdr *h = (wiz_hdr *)malloc(bytes);
  if (!h) wiz_panic("out of memory");
  h->rc = 1;
  h->tag = tag;
  h->size = size;
  wiz_live++;
  return h;
}

WIZ_API wiz_val wiz_ctor_new(uint32_t tag, uint32_t n) {
  wiz_ctor *o = (wiz_ctor *)wiz_alloc(sizeof(wiz_ctor) + n * sizeof(wiz_val), tag, n);
  return (wiz_val)o;
}
#define WIZ_SET(o, i, v) (((wiz_ctor *)(o))->fields[i] = (v))

WIZ_API void wiz_inc(wiz_val v) {
  if (!WIZ_IS_SCALAR(v)) ((wiz_hdr *)v)->rc++;
}

static void wiz_free(wiz_val v);

WIZ_API void wiz_dec(wiz_val v) {
  if (!WIZ_IS_SCALAR(v) && --((wiz_hdr *)v)->rc == 0) wiz_free(v);
}

static void wiz_free(wiz_val v) {
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->tag == WIZ_TAG_CLO) {
    wiz_clo *c = (wiz_clo *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(c->args[i]);
  } else if (h->tag == WIZ_TAG_BIG) {
    mpz_clear(((wiz_big *)v)->z);
  } else if (h->tag == WIZ_TAG_RAW) {
    /* raw machine words: nothing inside to drop */
  } else {
    wiz_ctor *o = (wiz_ctor *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(o->fields[i]);
  }
  wiz_live--;
  free(h);
}

WIZ_API uint32_t wiz_tag(wiz_val v) {
  return WIZ_IS_SCALAR(v) ? (uint32_t)WIZ_UNBOX(v) : ((wiz_hdr *)v)->tag;
}

/* ---- numbers: small scalars, or GMP objects ---- */

static int wiz_is_big(wiz_val v) { return !WIZ_IS_SCALAR(v) && ((wiz_hdr *)v)->tag == WIZ_TAG_BIG; }

static wiz_val wiz_big_norm(mpz_t z) {
  if (mpz_cmp_ui(z, 0) >= 0 && mpz_sizeinbase(z, 2) <= 62) {
    wiz_val r = WIZ_BOX(mpz_get_ui(z));
    mpz_clear(z);
    return r;
  }
  wiz_big *b = (wiz_big *)wiz_alloc(sizeof(wiz_big), WIZ_TAG_BIG, 0);
  memcpy(b->z, z, sizeof(mpz_t));
  return (wiz_val)b;
}

static void wiz_to_mpz(mpz_t z, wiz_val v) {
  if (WIZ_IS_SCALAR(v)) mpz_init_set_ui(z, (unsigned long)WIZ_UNBOX(v));
  else mpz_init_set(z, ((wiz_big *)v)->z);
}

WIZ_API wiz_val wiz_nat_lit(const char *digits) {
  mpz_t z;
  mpz_init_set_str(z, digits, 10);
  return wiz_big_norm(z);
}

WIZ_API wiz_val wiz_nat_add(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) {
    uintptr_t r = WIZ_UNBOX(a) + WIZ_UNBOX(b);
    if (r <= WIZ_MAX_SMALL) return WIZ_BOX(r);
  }
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  mpz_add(x, x, y); mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

WIZ_API wiz_val wiz_nat_sub(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(a) > WIZ_UNBOX(b) ? WIZ_UNBOX(a) - WIZ_UNBOX(b) : 0);
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  if (mpz_cmp(x, y) <= 0) mpz_set_ui(x, 0); else mpz_sub(x, x, y);
  mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

WIZ_API wiz_val wiz_nat_mul(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) {
    uintptr_t r;
    if (!__builtin_mul_overflow(WIZ_UNBOX(a), WIZ_UNBOX(b), &r) && r <= WIZ_MAX_SMALL) return WIZ_BOX(r);
  }
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  mpz_mul(x, x, y); mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

WIZ_API wiz_val wiz_nat_succ(wiz_val a) { return wiz_nat_add(a, WIZ_BOX(1)); }
WIZ_API wiz_val wiz_nat_pred(wiz_val a) { return wiz_nat_sub(a, WIZ_BOX(1)); }

static int wiz_nat_eq(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return a == b;
  if (WIZ_IS_SCALAR(a) || WIZ_IS_SCALAR(b)) return 0;
  return mpz_cmp(((wiz_big *)a)->z, ((wiz_big *)b)->z) == 0;
}

/* the prelude's `Bool` payload: ⟨tag, ⟨◾, ◾⟩⟩ */
WIZ_API wiz_val wiz_nat_beq(wiz_val a, wiz_val b) {
  int eq = wiz_nat_eq(a, b);
  wiz_dec(a); wiz_dec(b);
  wiz_val u = wiz_ctor_new(0, 2);
  WIZ_SET(u, 0, WIZ_BOX(0)); WIZ_SET(u, 1, WIZ_BOX(0));
  wiz_val r = wiz_ctor_new(0, 2);
  WIZ_SET(r, 0, WIZ_BOX(eq ? 1 : 0)); WIZ_SET(r, 1, u);
  return r;
}

/* ---- fields: a number looks like its unary payload (`natView`) ---- */

WIZ_API wiz_val wiz_proj(wiz_val v, uint32_t i) {
  if (WIZ_IS_SCALAR(v) || wiz_is_big(v)) {
    int zero = WIZ_IS_SCALAR(v) ? WIZ_UNBOX(v) == 0 : 0;
    if (i == 0) return WIZ_BOX(zero ? 0 : 1);
    wiz_val u = wiz_ctor_new(0, 2);
    WIZ_SET(u, 0, WIZ_BOX(0)); WIZ_SET(u, 1, WIZ_BOX(0));
    if (zero) return u;
    wiz_inc(v);
    wiz_val r = wiz_ctor_new(0, 2);
    WIZ_SET(r, 0, wiz_nat_pred(v)); WIZ_SET(r, 1, u);
    return r;
  }
  wiz_val f = ((wiz_ctor *)v)->fields[i];
  wiz_inc(f);
  return f;
}

/* `0` for an observed coinductive value, `1` for coit, `2` for scofix */
WIZ_API wiz_val wiz_lazy_tag(wiz_val v) {
  uint32_t t = WIZ_IS_SCALAR(v) ? 0 : ((wiz_hdr *)v)->tag;
  wiz_dec(v);
  return WIZ_BOX(t == 1000 ? 1 : t == 1001 ? 2 : 0);
}

/* ---- closures ---- */

WIZ_API wiz_val wiz_clo_new(wiz_boxed_fn fn, uint32_t arity, uint32_t n, wiz_val *args) {
  wiz_clo *c = (wiz_clo *)wiz_alloc(sizeof(wiz_clo) + n * sizeof(wiz_val), WIZ_TAG_CLO, n);
  c->fn = fn;
  c->arity = arity;
  for (uint32_t i = 0; i < n; i++) c->args[i] = args[i];
  return (wiz_val)c;
}

/* Apply a closure (owned) to `n` arguments (owned). */
WIZ_API wiz_val wiz_apply(wiz_val f, uint32_t n, wiz_val *args) {
  if (WIZ_IS_SCALAR(f) || ((wiz_hdr *)f)->tag != WIZ_TAG_CLO) wiz_panic("applying a non-function");
  wiz_clo *c = (wiz_clo *)f;
  uint32_t m = c->h.size, total = m + n;
  wiz_val *all = (wiz_val *)alloca(total * sizeof(wiz_val));
  for (uint32_t i = 0; i < m; i++) all[i] = c->args[i];
  for (uint32_t i = 0; i < n; i++) all[m + i] = args[i];
  wiz_boxed_fn fn = c->fn;
  uint32_t arity = c->arity;
  /* take the captured arguments: move them out of a unique closure, else share them */
  if (c->h.rc == 1) { wiz_live--; free(c); }
  else { for (uint32_t i = 0; i < m; i++) wiz_inc(all[i]); c->h.rc--; }
  if (total == arity) return fn(all);
  if (total < arity) return wiz_clo_new(fn, arity, total, all);
  wiz_val r = fn(all);
  return wiz_apply(r, total - arity, all + arity);
}

/* ---- reuse (Perceus): `reset` keeps a unique object's cell, `reuse` fills it ---- */

WIZ_API wiz_val wiz_reset(wiz_val x) {
  if (!WIZ_IS_SCALAR(x)) {
    wiz_hdr *h = (wiz_hdr *)x;
    if (h->rc == 1 && h->tag != WIZ_TAG_CLO && h->tag != WIZ_TAG_BIG) {
      for (uint32_t i = 0; i < h->size; i++) wiz_dec(((wiz_ctor *)x)->fields[i]);
      return x;
    }
  }
  wiz_dec(x);
  return WIZ_BOX(0);
}

WIZ_API wiz_val wiz_reuse(wiz_val tok, uint32_t tag, uint32_t n) {
  if (!WIZ_IS_SCALAR(tok)) {
    wiz_hdr *h = (wiz_hdr *)tok;
    if (h->size == n) { h->tag = tag; return tok; }
    wiz_live--;
    free(h);
  }
  return wiz_ctor_new(tag, n);
}

WIZ_API void wiz_unreachable(void) { wiz_panic("reached an impossible case"); }

/* ---- the FFI (stage 9): machine types and marshalling ---- */

/* UInt64 and Float64 are boxed raw words */
WIZ_API wiz_val wiz_raw_box(uint64_t bits) {
  wiz_ctor *o = (wiz_ctor *)wiz_alloc(sizeof(wiz_ctor) + sizeof(uint64_t), WIZ_TAG_RAW, 1);
  memcpy(o->fields, &bits, sizeof(uint64_t));
  return (wiz_val)o;
}
static uint64_t wiz_raw_bits(wiz_val v) {
  uint64_t b;
  memcpy(&b, ((wiz_ctor *)v)->fields, sizeof(uint64_t));
  return b;
}

/* each `wiz_in_*` consumes the Wiz value; each `wiz_out_*` makes one */
WIZ_API uint64_t wiz_in_u64(wiz_val v) { uint64_t b = wiz_raw_bits(v); wiz_dec(v); return b; }
WIZ_API wiz_val wiz_out_u64(uint64_t b) { return wiz_raw_box(b); }
WIZ_API double wiz_in_f64(wiz_val v) { uint64_t b = wiz_in_u64(v); double d; memcpy(&d, &b, 8); return d; }
WIZ_API wiz_val wiz_out_f64(double d) { uint64_t b; memcpy(&b, &d, 8); return wiz_raw_box(b); }
WIZ_API uint64_t wiz_in_nat(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) return WIZ_UNBOX(v);
  if (mpz_sizeinbase(((wiz_big *)v)->z, 2) > 64) wiz_panic("a number is too big for a C integer");
  uint64_t r = mpz_get_ui(((wiz_big *)v)->z);
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_out_nat(uint64_t n) {
  if (n <= WIZ_MAX_SMALL) return WIZ_BOX(n);
  mpz_t z;
  mpz_init_set_ui(z, n);
  return wiz_big_norm(z);
}

/* a constructor value as the erased payload: ⟨tag, ⟨f₁, … ⟨◾, ◾⟩⟩⟩ */
static wiz_val wiz_con(uint32_t tag, uint32_t n, wiz_val *fields) {
  wiz_val rest = wiz_ctor_new(0, 2);
  WIZ_SET(rest, 0, WIZ_BOX(0)); WIZ_SET(rest, 1, WIZ_BOX(0));
  for (uint32_t i = n; i > 0; i--) {
    wiz_val c = wiz_ctor_new(0, 2);
    WIZ_SET(c, 0, fields[i - 1]); WIZ_SET(c, 1, rest);
    rest = c;
  }
  wiz_val r = wiz_ctor_new(0, 2);
  WIZ_SET(r, 0, WIZ_BOX(tag)); WIZ_SET(r, 1, rest);
  return r;
}
static wiz_val wiz_field_ref(wiz_val v, uint32_t i) { /* borrowed */
  wiz_val rest = ((wiz_ctor *)v)->fields[1];
  for (uint32_t k = 0; k < i; k++) rest = ((wiz_ctor *)rest)->fields[1];
  return ((wiz_ctor *)rest)->fields[0];
}

WIZ_API int wiz_in_bool(wiz_val v) { int b = (int)wiz_tag(((wiz_ctor *)v)->fields[0]); wiz_dec(v); return b; }
WIZ_API wiz_val wiz_out_bool(int b) { return wiz_con(b ? 1 : 0, 0, NULL); }

/* String := String.mk (List Char), Char := Char.mk Nat; C strings are UTF-8 */
WIZ_API char *wiz_in_string(wiz_val s) {
  size_t cap = 16, len = 0;
  char *buf = (char *)malloc(cap);
  wiz_val l = wiz_field_ref(s, 0);
  while (wiz_tag(((wiz_ctor *)l)->fields[0]) == 1) {
    wiz_val ch = wiz_field_ref(l, 0);
    wiz_val cp = wiz_field_ref(ch, 0);
    uint32_t c = WIZ_IS_SCALAR(cp) ? (uint32_t)WIZ_UNBOX(cp) : 0xFFFD;
    if (len + 5 > cap) { cap *= 2; buf = (char *)realloc(buf, cap); }
    if (c < 0x80) buf[len++] = (char)c;
    else if (c < 0x800) { buf[len++] = 0xC0 | (c >> 6); buf[len++] = 0x80 | (c & 0x3F); }
    else if (c < 0x10000) { buf[len++] = 0xE0 | (c >> 12); buf[len++] = 0x80 | ((c >> 6) & 0x3F); buf[len++] = 0x80 | (c & 0x3F); }
    else { buf[len++] = 0xF0 | (c >> 18); buf[len++] = 0x80 | ((c >> 12) & 0x3F); buf[len++] = 0x80 | ((c >> 6) & 0x3F); buf[len++] = 0x80 | (c & 0x3F); }
    l = wiz_field_ref(l, 1);
  }
  buf[len] = 0;
  wiz_dec(s);
  return buf;
}
WIZ_API wiz_val wiz_out_string(const char *s) {
  /* decode UTF-8 into code points, then build the list from the end */
  size_t n = strlen(s), k = 0;
  uint32_t *cps = (uint32_t *)malloc((n + 1) * sizeof(uint32_t));
  for (size_t i = 0; i < n;) {
    unsigned char c = (unsigned char)s[i];
    uint32_t cp; int len;
    if (c < 0x80) { cp = c; len = 1; }
    else if ((c >> 5) == 6) { cp = c & 0x1F; len = 2; }
    else if ((c >> 4) == 14) { cp = c & 0x0F; len = 3; }
    else { cp = c & 0x07; len = 4; }
    for (int j = 1; j < len && i + j < n; j++) cp = (cp << 6) | ((unsigned char)s[i + j] & 0x3F);
    cps[k++] = cp;
    i += len;
  }
  wiz_val list = wiz_con(0, 0, NULL);
  for (size_t i = k; i > 0; i--) {
    wiz_val chf[1] = {WIZ_BOX(cps[i - 1])};
    wiz_val fs[2] = {wiz_con(0, 1, chf), list};
    list = wiz_con(1, 2, fs);
  }
  free(cps);
  wiz_val sf[1] = {list};
  return wiz_con(0, 1, sf);
}

/* an `IO` result: the pair (value, world) */
WIZ_API wiz_val wiz_io_result(wiz_val v, wiz_val world) {
  wiz_val p = wiz_ctor_new(0, 2);
  WIZ_SET(p, 0, v); WIZ_SET(p, 1, world);
  return p;
}

/* functions for the library to bind */
WIZ_API void wiz_io_println(const char *s) { puts(s); fflush(stdout); }
WIZ_API void wiz_io_print(const char *s) { fputs(s, stdout); fflush(stdout); }
WIZ_API uint64_t wiz_u64_id(uint64_t a) { return a; }
WIZ_API uint64_t wiz_u64_add(uint64_t a, uint64_t b) { return a + b; }
WIZ_API uint64_t wiz_u64_sub(uint64_t a, uint64_t b) { return a - b; }
WIZ_API uint64_t wiz_u64_mul(uint64_t a, uint64_t b) { return a * b; }
WIZ_API uint64_t wiz_u64_div(uint64_t a, uint64_t b) { return b ? a / b : 0; }
WIZ_API uint64_t wiz_u64_mod(uint64_t a, uint64_t b) { return b ? a % b : a; }
WIZ_API int wiz_u64_lt(uint64_t a, uint64_t b) { return a < b; }
WIZ_API int wiz_u64_eq(uint64_t a, uint64_t b) { return a == b; }
WIZ_API double wiz_f64_of_nat(uint64_t a) { return (double)a; }
WIZ_API double wiz_f64_add(double a, double b) { return a + b; }
WIZ_API double wiz_f64_sub(double a, double b) { return a - b; }
WIZ_API double wiz_f64_mul(double a, double b) { return a * b; }
WIZ_API double wiz_f64_div(double a, double b) { return a / b; }
WIZ_API int wiz_f64_lt(double a, double b) { return a < b; }
WIZ_API const char *wiz_f64_show(double a) { static char buf[64]; snprintf(buf, sizeof buf, "%.17g", a); return buf; }
WIZ_API const char *wiz_nat_show(uint64_t a) { static char buf[32]; snprintf(buf, sizeof buf, "%llu", (unsigned long long)a); return buf; }

/* ---- output: a generic tree, read back by the compiler using the type ---- */

static void wiz_print(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) { printf("%lu", (unsigned long)WIZ_UNBOX(v)); return; }
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->tag == WIZ_TAG_BIG) { mpz_out_str(stdout, 10, ((wiz_big *)v)->z); return; }
  if (h->tag == WIZ_TAG_CLO) { printf("<fn>"); return; }
  if (h->tag == WIZ_TAG_RAW) { printf("#%llu", (unsigned long long)wiz_raw_bits(v)); return; }
  printf("(%u", h->tag);
  for (uint32_t i = 0; i < h->size; i++) { putchar(' '); wiz_print(((wiz_ctor *)v)->fields[i]); }
  putchar(')');
}

/* WIZ_SET as a function, for the LLVM backend */
WIZ_API void wiz_set(wiz_val o, uint32_t i, wiz_val v) { WIZ_SET(o, i, v); }

/* run `main : IO A`: apply it to the world, and drop the result */
WIZ_API int wiz_finish_io(wiz_val main) {
  wiz_val w = WIZ_BOX(0);
  wiz_val r = wiz_apply(main, 1, &w);
  wiz_dec(r);
  if (wiz_live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)wiz_live); return 2; }
  return 0;
}

WIZ_API int wiz_finish(wiz_val r) {
  wiz_print(r);
  putchar('\n');
  wiz_dec(r);
  if (wiz_live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)wiz_live); return 2; }
  return 0;
}
