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

#define WIZ_BOX(n) ((((wiz_val)(n)) << 1) | 1)
#define WIZ_UNBOX(v) ((v) >> 1)
#define WIZ_IS_SCALAR(v) ((v) & 1)
#define WIZ_MAX_SMALL (((uintptr_t)1 << 62) - 1)

enum { WIZ_TAG_CLO = 0xFFFF0000u, WIZ_TAG_BIG = 0xFFFF0001u };

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

static wiz_val wiz_ctor_new(uint32_t tag, uint32_t n) {
  wiz_ctor *o = (wiz_ctor *)wiz_alloc(sizeof(wiz_ctor) + n * sizeof(wiz_val), tag, n);
  return (wiz_val)o;
}
#define WIZ_SET(o, i, v) (((wiz_ctor *)(o))->fields[i] = (v))

static inline void wiz_inc(wiz_val v) {
  if (!WIZ_IS_SCALAR(v)) ((wiz_hdr *)v)->rc++;
}

static void wiz_free(wiz_val v);

static inline void wiz_dec(wiz_val v) {
  if (!WIZ_IS_SCALAR(v) && --((wiz_hdr *)v)->rc == 0) wiz_free(v);
}

static void wiz_free(wiz_val v) {
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->tag == WIZ_TAG_CLO) {
    wiz_clo *c = (wiz_clo *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(c->args[i]);
  } else if (h->tag == WIZ_TAG_BIG) {
    mpz_clear(((wiz_big *)v)->z);
  } else {
    wiz_ctor *o = (wiz_ctor *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(o->fields[i]);
  }
  wiz_live--;
  free(h);
}

static inline uint32_t wiz_tag(wiz_val v) {
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

static wiz_val wiz_nat_lit(const char *digits) {
  mpz_t z;
  mpz_init_set_str(z, digits, 10);
  return wiz_big_norm(z);
}

static wiz_val wiz_nat_add(wiz_val a, wiz_val b) {
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

static wiz_val wiz_nat_sub(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(a) > WIZ_UNBOX(b) ? WIZ_UNBOX(a) - WIZ_UNBOX(b) : 0);
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  if (mpz_cmp(x, y) <= 0) mpz_set_ui(x, 0); else mpz_sub(x, x, y);
  mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

static wiz_val wiz_nat_mul(wiz_val a, wiz_val b) {
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

static wiz_val wiz_nat_succ(wiz_val a) { return wiz_nat_add(a, WIZ_BOX(1)); }
static wiz_val wiz_nat_pred(wiz_val a) { return wiz_nat_sub(a, WIZ_BOX(1)); }

static int wiz_nat_eq(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return a == b;
  if (WIZ_IS_SCALAR(a) || WIZ_IS_SCALAR(b)) return 0;
  return mpz_cmp(((wiz_big *)a)->z, ((wiz_big *)b)->z) == 0;
}

/* the prelude's `Bool` payload: ⟨tag, ⟨◾, ◾⟩⟩ */
static wiz_val wiz_nat_beq(wiz_val a, wiz_val b) {
  int eq = wiz_nat_eq(a, b);
  wiz_dec(a); wiz_dec(b);
  wiz_val u = wiz_ctor_new(0, 2);
  WIZ_SET(u, 0, WIZ_BOX(0)); WIZ_SET(u, 1, WIZ_BOX(0));
  wiz_val r = wiz_ctor_new(0, 2);
  WIZ_SET(r, 0, WIZ_BOX(eq ? 1 : 0)); WIZ_SET(r, 1, u);
  return r;
}

/* ---- fields: a number looks like its unary payload (`natView`) ---- */

static wiz_val wiz_proj(wiz_val v, uint32_t i) {
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
static wiz_val wiz_lazy_tag(wiz_val v) {
  uint32_t t = WIZ_IS_SCALAR(v) ? 0 : ((wiz_hdr *)v)->tag;
  wiz_dec(v);
  return WIZ_BOX(t == 1000 ? 1 : t == 1001 ? 2 : 0);
}

/* ---- closures ---- */

static wiz_val wiz_clo_new(wiz_boxed_fn fn, uint32_t arity, uint32_t n, wiz_val *args) {
  wiz_clo *c = (wiz_clo *)wiz_alloc(sizeof(wiz_clo) + n * sizeof(wiz_val), WIZ_TAG_CLO, n);
  c->fn = fn;
  c->arity = arity;
  for (uint32_t i = 0; i < n; i++) c->args[i] = args[i];
  return (wiz_val)c;
}

/* Apply a closure (owned) to `n` arguments (owned). */
static wiz_val wiz_apply(wiz_val f, uint32_t n, wiz_val *args) {
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

static wiz_val wiz_reset(wiz_val x) {
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

static wiz_val wiz_reuse(wiz_val tok, uint32_t tag, uint32_t n) {
  if (!WIZ_IS_SCALAR(tok)) {
    wiz_hdr *h = (wiz_hdr *)tok;
    if (h->size == n) { h->tag = tag; return tok; }
    wiz_live--;
    free(h);
  }
  return wiz_ctor_new(tag, n);
}

static void wiz_unreachable(void) { wiz_panic("reached an impossible case"); }

/* ---- output: a generic tree, read back by the compiler using the type ---- */

static void wiz_print(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) { printf("%lu", (unsigned long)WIZ_UNBOX(v)); return; }
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->tag == WIZ_TAG_BIG) { mpz_out_str(stdout, 10, ((wiz_big *)v)->z); return; }
  if (h->tag == WIZ_TAG_CLO) { printf("<fn>"); return; }
  printf("(%u", h->tag);
  for (uint32_t i = 0; i < h->size; i++) { putchar(' '); wiz_print(((wiz_ctor *)v)->fields[i]); }
  putchar(')');
}

static int wiz_finish(wiz_val r) {
  wiz_print(r);
  putchar('\n');
  wiz_dec(r);
  if (wiz_live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)wiz_live); return 2; }
  return 0;
}
