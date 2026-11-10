/* The Wiz runtime (stage 8b), included at the top of every generated C file.

   A value is a machine word. If its lowest bit is 1 it is a **scalar** (a small
   number, a tag, or ◾) holding `v >> 1`; otherwise it points to an **object**: a
   header (reference count, tag, number of fields) and the fields. Closures and big
   numbers (GMP) are objects with reserved tags. Reference counts follow the IR's
   `dup`/`drop` (Perceus): every function owns its arguments. */

#include <alloca.h>
#include <pthread.h>
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

enum { WIZ_TAG_FIRST_SPECIAL = 0xFFFF0000u, WIZ_TAG_CLO = 0xFFFF0000u, WIZ_TAG_BIG = 0xFFFF0001u, WIZ_TAG_RAW = 0xFFFF0002u,
       WIZ_TAG_EXT = 0xFFFF0003u, WIZ_TAG_BYTES = 0xFFFF0004u, WIZ_TAG_ARRAY = 0xFFFF0005u,
       WIZ_TAG_STR = 0xFFFF0006u, WIZ_TAG_MAP = 0xFFFF0007u, WIZ_TAG_THUNK = 0xFFFF0008u };


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

/* a memoised suspension (`memo f`): applied like a closure, it runs `f` once and keeps
   the result; `fn` is 0 once it has */
typedef struct {
  wiz_hdr h;
  wiz_val fn;
  wiz_val val;
} wiz_thunk;

/* a foreign pointer, with the function that releases it (or NULL) */
typedef struct {
  wiz_hdr h;
  void *ptr;
  void (*fin)(void *);
} wiz_ext;

/* a byte buffer */
typedef struct {
  wiz_hdr h;
  size_t len, cap;
  unsigned char *data;
} wiz_bytes;

/* an array of Wiz values */
typedef struct {
  wiz_hdr h;
  size_t len, cap;
  wiz_val *data;
} wiz_array;

/* UTF-8 text (immutable) */
typedef struct {
  wiz_hdr h;
  size_t len; /* bytes */
  char data[];
} wiz_str;

/* a hash map from text to Wiz values (open addressing) */
typedef struct {
  wiz_hdr h;
  size_t count, cap;
  wiz_val *keys; /* Str objects, or 0 for empty */
  wiz_val *vals;
} wiz_map;

static int64_t wiz_live = 0;

/* with WIZ_LEAKS set, remember every live object, to list the leaked ones at exit */
static int wiz_leaks = -1;
static void *wiz_watch = NULL;
static void **wiz_track_tab = NULL;
static size_t wiz_track_cap = 0, wiz_track_n = 0;
static size_t wiz_track_slot(void *p) {
  size_t i = ((uintptr_t)p >> 4) * 11400714819323198485ull & (wiz_track_cap - 1);
  while (wiz_track_tab[i] && wiz_track_tab[i] != p) i = (i + 1) & (wiz_track_cap - 1);
  return i;
}
static void wiz_track(void *p) {
  if (wiz_leaks < 0) {
    wiz_leaks = getenv("WIZ_LEAKS") != NULL;
    if (getenv("WIZ_WATCH")) wiz_watch = (void *)strtoull(getenv("WIZ_WATCH"), NULL, 16);
  }
  if (!wiz_leaks) return;
  if (2 * (wiz_track_n + 1) > wiz_track_cap) {
    void **old = wiz_track_tab; size_t oc = wiz_track_cap;
    wiz_track_cap = oc ? 2 * oc : 1024;
    wiz_track_tab = (void **)calloc(wiz_track_cap, sizeof(void *));
    wiz_track_n = 0;
    for (size_t i = 0; i < oc; i++) if (old[i] && old[i] != (void *)1) { wiz_track_tab[wiz_track_slot(old[i])] = old[i]; wiz_track_n++; }
    free(old);
  }
  wiz_track_tab[wiz_track_slot(p)] = p;
  wiz_track_n++;
}
static void wiz_untrack(void *p) {
  if (wiz_leaks != 1) return;
  /* rebuild the probe chain after removing */
  size_t i = wiz_track_slot(p);
  if (wiz_track_tab[i] != p) return;
  wiz_track_tab[i] = NULL; wiz_track_n--;
  for (size_t j = (i + 1) & (wiz_track_cap - 1); wiz_track_tab[j]; j = (j + 1) & (wiz_track_cap - 1)) {
    void *q = wiz_track_tab[j]; wiz_track_tab[j] = NULL; wiz_track_n--;
    wiz_track_tab[wiz_track_slot(q)] = q; wiz_track_n++;
  }
}

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
  wiz_track(h);
  return h;
}

WIZ_API wiz_val wiz_ctor_new(uint32_t tag, uint32_t n) {
  wiz_ctor *o = (wiz_ctor *)wiz_alloc(sizeof(wiz_ctor) + n * sizeof(wiz_val), tag, n);
  return (wiz_val)o;
}
#define WIZ_SET(o, i, v) (((wiz_ctor *)(o))->fields[i] = (v))

/* with WIZ_WATCH=<address> (and WIZ_LEAKS), log the reference count changes of one object */
static void wiz_watch_log(const char *what, wiz_val v, void *from) {
  if ((void *)v == wiz_watch) fprintf(stderr, "  %s %p: rc %ld, from %p\n", what, (void *)v, (long)((wiz_hdr *)v)->rc, from);
}
WIZ_API void wiz_inc(wiz_val v) {
  if (!WIZ_IS_SCALAR(v)) ((wiz_hdr *)v)->rc++;
  if (wiz_watch) wiz_watch_log("inc", v, __builtin_return_address(0));
}

static void wiz_free(wiz_val v);

WIZ_API void wiz_dec(wiz_val v) {
  if (wiz_watch) wiz_watch_log("dec", v, __builtin_return_address(0));
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
  } else if (h->tag == WIZ_TAG_EXT) {
    wiz_ext *e = (wiz_ext *)v;
    if (e->fin && e->ptr) e->fin(e->ptr);
  } else if (h->tag == WIZ_TAG_BYTES) {
    free(((wiz_bytes *)v)->data);
  } else if (h->tag == WIZ_TAG_ARRAY) {
    wiz_array *a = (wiz_array *)v;
    for (size_t i = 0; i < a->len; i++) wiz_dec(a->data[i]);
    free(a->data);
  } else if (h->tag == WIZ_TAG_STR) {
    /* the text is inline */
  } else if (h->tag == WIZ_TAG_THUNK) {
    wiz_thunk *t = (wiz_thunk *)v;
    if (t->fn) wiz_dec(t->fn); else wiz_dec(t->val);
  } else if (h->tag == WIZ_TAG_MAP) {
    wiz_map *m = (wiz_map *)v;
    for (size_t i = 0; i < m->cap; i++) if (m->keys[i]) { wiz_dec(m->keys[i]); wiz_dec(m->vals[i]); }
    free(m->keys); free(m->vals);
  } else {
    wiz_ctor *o = (wiz_ctor *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(o->fields[i]);
  }
  wiz_live--;
  wiz_untrack(h);
  free(h);
}

/* a shared constant: never freed, and not counted as live (so not a leak) */
static void wiz_immortal(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) return;
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->rc >= ((int64_t)1 << 40)) return;
  h->rc = (int64_t)1 << 50;
  wiz_live--;
  wiz_untrack(h);
  if (h->tag < WIZ_TAG_FIRST_SPECIAL)
    for (uint32_t i = 0; i < h->size; i++) wiz_immortal(((wiz_ctor *)v)->fields[i]);
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

/* the prelude's `Bool`: a constructor without fields is its tag. The comparisons
   borrow their arguments (stage 8e, `primBorrows`): the caller keeps its references. */
WIZ_API wiz_val wiz_nat_beq(wiz_val a, wiz_val b) {
  int eq = wiz_nat_eq(a, b);
  return WIZ_BOX(eq ? 1 : 0);
}
WIZ_API wiz_val wiz_nat_blt(wiz_val a, wiz_val b) {
  int lt;
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) lt = WIZ_UNBOX(a) < WIZ_UNBOX(b);
  else { mpz_t x, y; wiz_to_mpz(x, a); wiz_to_mpz(y, b); lt = mpz_cmp(x, y) < 0; mpz_clear(x); mpz_clear(y); }
  return WIZ_BOX(lt ? 1 : 0);
}

/* division, powers and bits; as the Prelude defines them: n / 0 = 0, n % 0 = n,
   log2 0 = 0 */
enum { WIZ_OP_DIV, WIZ_OP_MOD, WIZ_OP_AND, WIZ_OP_OR, WIZ_OP_XOR };
static wiz_val wiz_nat_big_op(int op, wiz_val a, wiz_val b) {
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  switch (op) {
  case WIZ_OP_DIV: if (mpz_sgn(y) == 0) mpz_set_ui(x, 0); else mpz_fdiv_q(x, x, y); break;
  case WIZ_OP_MOD: if (mpz_sgn(y) != 0) mpz_fdiv_r(x, x, y); break;
  case WIZ_OP_AND: mpz_and(x, x, y); break;
  case WIZ_OP_OR: mpz_ior(x, x, y); break;
  default: mpz_xor(x, x, y); break;
  }
  mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_div(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(b) ? WIZ_UNBOX(a) / WIZ_UNBOX(b) : 0);
  return wiz_nat_big_op(WIZ_OP_DIV, a, b);
}
WIZ_API wiz_val wiz_nat_mod(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(b) ? WIZ_UNBOX(a) % WIZ_UNBOX(b) : WIZ_UNBOX(a));
  return wiz_nat_big_op(WIZ_OP_MOD, a, b);
}
WIZ_API wiz_val wiz_nat_land(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return WIZ_BOX(WIZ_UNBOX(a) & WIZ_UNBOX(b));
  return wiz_nat_big_op(WIZ_OP_AND, a, b);
}
WIZ_API wiz_val wiz_nat_lor(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return WIZ_BOX(WIZ_UNBOX(a) | WIZ_UNBOX(b));
  return wiz_nat_big_op(WIZ_OP_OR, a, b);
}
WIZ_API wiz_val wiz_nat_xor(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return WIZ_BOX(WIZ_UNBOX(a) ^ WIZ_UNBOX(b));
  return wiz_nat_big_op(WIZ_OP_XOR, a, b);
}
/* `a * 2^n`; a shift by a big number of a nonzero number has no representation */
WIZ_API wiz_val wiz_nat_shiftLeft(wiz_val a, wiz_val n) {
  if (WIZ_IS_SCALAR(a) && WIZ_UNBOX(a) == 0) { wiz_dec(n); return a; }
  if (!WIZ_IS_SCALAR(n)) wiz_panic("Nat.shiftLeft: the shift is too big");
  uintptr_t k = WIZ_UNBOX(n);
  if (WIZ_IS_SCALAR(a) && k < 62 && WIZ_UNBOX(a) <= (WIZ_MAX_SMALL >> k)) return WIZ_BOX(WIZ_UNBOX(a) << k);
  mpz_t x;
  wiz_to_mpz(x, a);
  mpz_mul_2exp(x, x, (mp_bitcnt_t)k);
  wiz_dec(a);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_shiftRight(wiz_val a, wiz_val n) {
  if (!WIZ_IS_SCALAR(n)) { wiz_dec(a); wiz_dec(n); return WIZ_BOX(0); }
  uintptr_t k = WIZ_UNBOX(n);
  if (WIZ_IS_SCALAR(a)) return WIZ_BOX(k >= 64 ? 0 : WIZ_UNBOX(a) >> k);
  mpz_t x;
  wiz_to_mpz(x, a);
  mpz_fdiv_q_2exp(x, x, (mp_bitcnt_t)k);
  wiz_dec(a);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_pow(wiz_val b, wiz_val e) {
  if (WIZ_IS_SCALAR(b) && WIZ_UNBOX(b) <= 1) {
    /* 0^0 = 1, 0^e = 0, 1^e = 1, even for a big e */
    int zero = WIZ_IS_SCALAR(e) && WIZ_UNBOX(e) == 0;
    wiz_dec(e);
    return WIZ_BOX(zero ? 1 : WIZ_UNBOX(b));
  }
  if (!WIZ_IS_SCALAR(e)) wiz_panic("Nat.pow: the exponent is too big");
  uintptr_t k = WIZ_UNBOX(e);
  if (WIZ_IS_SCALAR(b)) {
    uintptr_t r = 1, x = WIZ_UNBOX(b), i = 0;
    for (; i < k; i++)
      if (__builtin_mul_overflow(r, x, &r) || r > WIZ_MAX_SMALL) break;
    if (i == k) return WIZ_BOX(r);
  }
  mpz_t x;
  wiz_to_mpz(x, b);
  mpz_pow_ui(x, x, (unsigned long)k);
  wiz_dec(b);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_log2(wiz_val a) {
  if (WIZ_IS_SCALAR(a)) {
    uintptr_t x = WIZ_UNBOX(a);
    return WIZ_BOX(x == 0 ? 0 : 63 - __builtin_clzll((unsigned long long)x));
  }
  size_t bits = mpz_sizeinbase(((wiz_big *)a)->z, 2);
  wiz_dec(a);
  return WIZ_BOX(bits - 1);
}

/* ---- flat objects: tags and fields by runtime values (`pack`, `unpack`) ---- */

WIZ_API wiz_val wiz_tag_of(wiz_val v) {
  uint32_t t = wiz_tag(v);
  wiz_dec(v);
  return WIZ_BOX(t);
}
WIZ_API wiz_val wiz_nat_tag(wiz_val v) {
  int zero = WIZ_IS_SCALAR(v) && WIZ_UNBOX(v) == 0;
  wiz_dec(v);
  return WIZ_BOX(zero ? 0 : 1);
}
WIZ_API wiz_val wiz_field_at(wiz_val v, wiz_val n) {
  wiz_val f = ((wiz_ctor *)v)->fields[WIZ_UNBOX(n)];
  wiz_inc(f);
  wiz_dec(v);
  return f;
}
/* an object with the tag of `t` and the fields listed by `l` (nested pairs ending in ◾) */
WIZ_API wiz_val wiz_mk_obj(wiz_val t, wiz_val l) {
  uint32_t tag = wiz_tag(t), n = 0;
  wiz_dec(t);
  for (wiz_val c = l; !WIZ_IS_SCALAR(c); c = ((wiz_ctor *)c)->fields[1]) n++;
  if (n == 0) { wiz_dec(l); return WIZ_BOX(tag); }
  wiz_val r = wiz_ctor_new(tag, n);
  uint32_t i = 0;
  for (wiz_val c = l; !WIZ_IS_SCALAR(c); c = ((wiz_ctor *)c)->fields[1]) {
    wiz_val f = ((wiz_ctor *)c)->fields[0];
    wiz_inc(f);
    WIZ_SET(r, i++, f);
  }
  wiz_dec(l);
  return r;
}

/* ---- fields ---- */

/* A number's constructor tag (0 for zero) is field 0 of its unary view. Its other fields
   would be fresh objects (`natView`), but `proj` is borrowed since stage 8e: nobody would
   own, and so free, them. The lowering takes numbers apart with `natTag`/`nat.pred`, so
   reaching this is a compiler bug: stop instead of leaking. */
WIZ_API wiz_val wiz_proj(wiz_val v, uint32_t i) {
  if (WIZ_IS_SCALAR(v) || wiz_is_big(v)) {
    if (i == 0) return WIZ_BOX(WIZ_IS_SCALAR(v) && WIZ_UNBOX(v) == 0 ? 0 : 1);
    wiz_panic("internal error: proj of a field of a number (use natTag/nat.pred)");
  }
  /* borrowed: no new reference (the IR `dup`s it if it needs one) */
  return ((wiz_ctor *)v)->fields[i];
}

/* `0` for an observed coinductive value, `1` for coit, `2` for scofix, `3` for a lazy
   cell already observed (tag 1002: its one field is the payload) */
WIZ_API wiz_val wiz_lazy_tag(wiz_val v) {
  uint32_t t = WIZ_IS_SCALAR(v) ? 0 : ((wiz_hdr *)v)->tag;
  wiz_dec(v);
  return WIZ_BOX(t == 1000 ? 1 : t == 1001 ? 2 : t == 1002 ? 3 : 0);
}

/* Memoised observation: `out` has computed the payload `p` of the lazy cell `x` (both
   owned) and returns `p`. A shared cell is overwritten in place by an observed cell
   ⟨1002 p⟩, so its other references don't unfold it again (like a forced `memo`
   thunk). The payload's corecursive fields are new cells, never `x`: no cycle forms.
   A unique cell (rc 1) dies here, so there is nothing to keep (the plain-thunk case);
   an immortal cell (a hoisted constant) is not overwritten, or it would keep its
   observed prefix for ever.
   Threads: like `memo`, this assumes one mutator (reference counts are not atomic).
   With several, only a shared cell needs care: claim it by a CAS of its tag to a
   blackhole before computing, and make other observers wait for the payload. */
WIZ_API wiz_val wiz_lazy_set(wiz_val x, wiz_val p) {
  wiz_hdr *h = (wiz_hdr *)x;
  if (WIZ_IS_SCALAR(x) || h->rc == 1 || h->rc >= ((int64_t)1 << 40) || (h->tag != 1000 && h->tag != 1001)) {
    wiz_dec(x);
    return p;
  }
  wiz_ctor *o = (wiz_ctor *)x;
  uint32_t n = h->size;
  for (uint32_t i = 0; i < n; i++) wiz_dec(o->fields[i]);
  h->tag = 1002;
  h->size = 1;
  wiz_inc(p);
  o->fields[0] = p;
  h->rc--; /* shared: still alive */
  return p;
}

/* ---- closures ---- */

WIZ_API wiz_val wiz_clo_new(wiz_boxed_fn fn, uint32_t arity, uint32_t n, wiz_val *args) {
  wiz_clo *c = (wiz_clo *)wiz_alloc(sizeof(wiz_clo) + n * sizeof(wiz_val), WIZ_TAG_CLO, n);
  c->fn = fn;
  c->arity = arity;
  for (uint32_t i = 0; i < n; i++) c->args[i] = args[i];
  return (wiz_val)c;
}

/* `memo A f`: the suspension `f` (owned), run at most once */
WIZ_API wiz_val wiz_memo(wiz_val ty, wiz_val f) {
  (void)ty;
  wiz_thunk *t = (wiz_thunk *)wiz_alloc(sizeof(wiz_thunk), WIZ_TAG_THUNK, 0);
  t->fn = f;
  t->val = WIZ_BOX(0);
  return (wiz_val)t;
}

/* Apply a closure (owned) to `n` arguments (owned). */
WIZ_API wiz_val wiz_apply(wiz_val f, uint32_t n, wiz_val *args) {
  if (!WIZ_IS_SCALAR(f) && ((wiz_hdr *)f)->tag == WIZ_TAG_THUNK) {
    /* force: the first argument is the unit */
    wiz_thunk *t = (wiz_thunk *)f;
    if (t->fn) {
      wiz_val g = t->fn;
      t->fn = 0;
      t->val = wiz_apply(g, 1, args);
    } else wiz_dec(args[0]);
    wiz_val r = t->val;
    wiz_inc(r);
    wiz_dec(f);
    return n > 1 ? wiz_apply(r, n - 1, args + 1) : r;
  }
  if (WIZ_IS_SCALAR(f) || ((wiz_hdr *)f)->tag != WIZ_TAG_CLO) wiz_panic("applying a non-function");
  wiz_clo *c = (wiz_clo *)f;
  uint32_t m = c->h.size, total = m + n;
  wiz_val *all = (wiz_val *)alloca(total * sizeof(wiz_val));
  for (uint32_t i = 0; i < m; i++) all[i] = c->args[i];
  for (uint32_t i = 0; i < n; i++) all[m + i] = args[i];
  wiz_boxed_fn fn = c->fn;
  uint32_t arity = c->arity;
  /* take the captured arguments: move them out of a unique closure, else share them */
  if (c->h.rc == 1) { wiz_live--; wiz_untrack(c); free(c); }
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
    /* only a constructor's cell can be reused: closures, numbers and the runtime's own
       objects (arrays, strings, maps …) own more than their fields */
    if (h->rc == 1 && h->tag < WIZ_TAG_FIRST_SPECIAL) {
      for (uint32_t i = 0; i < h->size; i++) wiz_dec(((wiz_ctor *)x)->fields[i]);
      return x;
    }
  }
  wiz_dec(x);
  return WIZ_BOX(0);
}

/* drop specialisation (stage 8e): drop `x`, whose fields in `mask` were read and are
   still needed. Unique: they move out (the others are dropped) and the cell is freed;
   shared: they get a reference each and `x` is decremented. */
WIZ_API wiz_val wiz_drop_moved(wiz_val x, wiz_val mask) {
  if (WIZ_IS_SCALAR(x)) return WIZ_BOX(0);
  wiz_hdr *h = (wiz_hdr *)x;
  uint64_t m = WIZ_UNBOX(mask);
  if (h->tag >= WIZ_TAG_FIRST_SPECIAL) { wiz_dec(x); return WIZ_BOX(0); }
  wiz_val *fs = ((wiz_ctor *)x)->fields;
  if (h->rc == 1) {
    for (uint32_t i = 0; i < h->size; i++)
      if (i >= 62 || !((m >> i) & 1)) wiz_dec(fs[i]);
    wiz_live--;
    wiz_untrack(h);
    free(h);
  } else {
    for (uint32_t i = 0; i < h->size && i < 62; i++)
      if ((m >> i) & 1) wiz_inc(fs[i]);
    h->rc--;
  }
  return WIZ_BOX(0);
}

WIZ_API wiz_val wiz_reuse(wiz_val tok, uint32_t tag, uint32_t n) {
  if (!WIZ_IS_SCALAR(tok)) {
    wiz_hdr *h = (wiz_hdr *)tok;
    if (h->size == n) { h->tag = tag; return tok; }
    wiz_live--;
    wiz_untrack(h);
    free(h);
  }
  /* without fields the result is a scalar: `reuse w in ctor t` just frees the token */
  if (n == 0) return WIZ_BOX(tag);
  return wiz_ctor_new(tag, n);
}

/* list the objects still alive (with WIZ_LEAKS set) */
static void wiz_report_leaks(void) {
  if (wiz_leaks != 1) return;
  for (size_t i = 0; i < wiz_track_cap; i++) {
    wiz_hdr *h = (wiz_hdr *)wiz_track_tab[i];
    if (!h) continue;
    fprintf(stderr, "  leaked %p: tag %u, %u fields, rc %u:", (void *)h, h->tag, h->size, (unsigned)h->rc);
    if (h->tag < 1000) {
      wiz_ctor *o = (wiz_ctor *)h;
      for (uint32_t k = 0; k < h->size; k++) {
        wiz_val f = o->fields[k];
        if (WIZ_IS_SCALAR(f)) fprintf(stderr, " %lu", (unsigned long)WIZ_UNBOX(f));
        else fprintf(stderr, " <tag %u>", ((wiz_hdr *)f)->tag);
      }
    }
    fprintf(stderr, "\n");
  }
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

/* ---- machine words (lib/Word.wiz, stages 22c-d) ----
   `UIntN w` and `IntN w` (and `BitVec n`, which is `UIntN n`) are, in the model,
   `mk (toNat : Nat)` with the width a phantom parameter (stage 22e), so the model's
   object is `⟨0 bits⟩`: the bits as a number below 2^w (two's complement for `IntN`). Compiled code represents them natively
   (`attribute [implemented_by mk get] UIntN.mk`): a value is its bits b,
     * a scalar if b < 2^63 (no allocation),
     * a raw box (WIZ_TAG_RAW) if 2^63 <= b < 2^64,
     * a big number (GMP) if b >= 2^64 (widths above 64 only).
   The representation depends only on b, not on the width (generic code over `UIntN w`
   doesn't know w), so each value has exactly one. `wiz_word_of_bits`/`wiz_word_to_bits`
   convert from and to the number (the model's constructor and field); the operations
   below implement the Wiz definitions: on uint64_t up to 64 bits, with GMP beyond.
   Each consumes its arguments. */
enum { WIZ_W_ADD, WIZ_W_SUB, WIZ_W_MUL, WIZ_W_UDIV, WIZ_W_UMOD, WIZ_W_NOT, WIZ_W_SHL,
       WIZ_W_SDIV, WIZ_W_SREM, WIZ_W_ASHR, WIZ_W_SLT, WIZ_W_SLE,
       WIZ_W_AND, WIZ_W_OR, WIZ_W_XOR, WIZ_W_LSHR, WIZ_W_EQ, WIZ_W_ULT, WIZ_W_ULE, WIZ_W_BIT };
/* for operations whose result never exceeds their arguments: no width needed */
#define WIZ_W_ANY (~(uint64_t)0)
#define WIZ_WORD_SCALAR_MAX ((((uint64_t)1) << 63) - 1)
static inline wiz_val wiz_word_out(uint64_t b) { return b <= WIZ_WORD_SCALAR_MAX ? WIZ_BOX(b) : wiz_raw_box(b); }
/* the bits of a word below 2^64 (without consuming it) */
static inline int wiz_word_in(wiz_val v, uint64_t *b) {
  if (WIZ_IS_SCALAR(v)) { *b = WIZ_UNBOX(v); return 1; }
  if (((wiz_hdr *)v)->tag == WIZ_TAG_RAW) { *b = wiz_raw_bits(v); return 1; }
  return 0;
}
static void wiz_word_mpz(mpz_t z, wiz_val v) {
  uint64_t b;
  if (wiz_word_in(v, &b)) mpz_init_set_ui(z, (unsigned long)b);
  else mpz_init_set(z, ((wiz_big *)v)->z);
}
/* a number >= 0 (cleared) as a word */
static wiz_val wiz_word_of_mpz(mpz_t z) {
  if (mpz_sizeinbase(z, 2) <= 64) { uint64_t b = mpz_get_ui(z); mpz_clear(z); return wiz_word_out(b); }
  wiz_big *o = (wiz_big *)wiz_alloc(sizeof(wiz_big), WIZ_TAG_BIG, 0);
  memcpy(o->z, z, sizeof(mpz_t));
  return (wiz_val)o;
}
/* the model's constructor: a number below 2^w (a Nat) as a word */
WIZ_API wiz_val wiz_word_of_bits(wiz_val n) {
  if (WIZ_IS_SCALAR(n)) return n;  /* below 2^62: the same scalar */
  if (mpz_sizeinbase(((wiz_big *)n)->z, 2) > 64) return n;  /* at least 2^64: the same number */
  uint64_t b = mpz_get_ui(((wiz_big *)n)->z);
  wiz_dec(n);
  return wiz_word_out(b);
}
/* the model's field: a word as its number (a Nat) */
WIZ_API wiz_val wiz_word_to_bits(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) return WIZ_UNBOX(v) <= WIZ_MAX_SMALL ? v : wiz_out_nat(WIZ_UNBOX(v));
  if (((wiz_hdr *)v)->tag == WIZ_TAG_RAW) { uint64_t b = wiz_raw_bits(v); wiz_dec(v); return wiz_out_nat(b); }
  return v;
}
/* a shift or bit index (a Nat): beyond 2^64, as good as infinite */
static uint64_t wiz_word_amount(wiz_val k) {
  if (WIZ_IS_SCALAR(k)) return WIZ_UNBOX(k);
  wiz_dec(k);
  return ~(uint64_t)0;
}
/* bits of width w as a signed number (in place) */
static void wiz_word_signed(mpz_t x, uint64_t w) {
  if (w > 0 && mpz_tstbit(x, w - 1)) { mpz_t p; mpz_init(p); mpz_setbit(p, w); mpz_sub(x, x, p); mpz_clear(p); }
}
static inline uint64_t wiz_word_mask(uint64_t w) { return w >= 64 ? ~(uint64_t)0 : (((uint64_t)1 << w) - 1); }
/* op on words of width w (k: a shift or bit index). Comparisons and `bit` give the
   scalar 0 or 1; everything else a word. */
static inline wiz_val wiz_word_op(int op, uint64_t w, wiz_val a, wiz_val b, uint64_t k) {
  uint64_t x, y = 0;
  if ((w <= 64 || w == WIZ_W_ANY) && wiz_word_in(a, &x) && wiz_word_in(b, &y)) {
    uint64_t mask = wiz_word_mask(w), r;
    int s = w >= 64 ? 0 : 64 - (int)w;
    int64_t sx = w ? (int64_t)(x << s) >> s : 0, sy = w ? (int64_t)(y << s) >> s : 0;
    if (!WIZ_IS_SCALAR(a)) wiz_dec(a);
    if (!WIZ_IS_SCALAR(b)) wiz_dec(b);
    switch (op) {
    case WIZ_W_ADD: r = x + y; break;
    case WIZ_W_SUB: r = x - y; break;
    case WIZ_W_MUL: r = x * y; break;
    case WIZ_W_UDIV: r = y ? x / y : 0; break;
    case WIZ_W_UMOD: r = y ? x % y : x; break;
    case WIZ_W_NOT: r = ~x; break;
    case WIZ_W_SHL: r = k >= w ? 0 : x << k; break;
    case WIZ_W_SDIV: r = y == 0 ? 0 : (sy == -1 ? (uint64_t)0 - x : (uint64_t)(sx / sy)); break;
    case WIZ_W_SREM: r = y == 0 ? x : (sy == -1 ? 0 : (uint64_t)(sx % sy)); break;
    case WIZ_W_ASHR: r = (uint64_t)(sx >> (k >= w ? (w ? w - 1 : 0) : k)); break;
    case WIZ_W_SLT: return WIZ_BOX(sx < sy);
    case WIZ_W_SLE: return WIZ_BOX(sx <= sy);
    case WIZ_W_AND: r = x & y; break;
    case WIZ_W_OR: r = x | y; break;
    case WIZ_W_XOR: r = x ^ y; break;
    case WIZ_W_LSHR: r = k >= 64 ? 0 : x >> k; break;
    case WIZ_W_EQ: return WIZ_BOX(x == y);
    case WIZ_W_ULT: return WIZ_BOX(x < y);
    case WIZ_W_ULE: return WIZ_BOX(x <= y);
    default: return WIZ_BOX(k < 64 && ((x >> k) & 1));
    }
    return wiz_word_out(r & mask);
  }
  mpz_t mx, my;
  wiz_word_mpz(mx, a); wiz_word_mpz(my, b);
  wiz_dec(a); wiz_dec(b);
  int cmp = 2;
  switch (op) {
  case WIZ_W_ADD: mpz_add(mx, mx, my); break;
  case WIZ_W_SUB: mpz_sub(mx, mx, my); break;
  case WIZ_W_MUL: mpz_mul(mx, mx, my); break;
  case WIZ_W_UDIV: if (mpz_sgn(my) == 0) mpz_set_ui(mx, 0); else mpz_fdiv_q(mx, mx, my); break;
  case WIZ_W_UMOD: if (mpz_sgn(my) != 0) mpz_fdiv_r(mx, mx, my); break;
  case WIZ_W_NOT: mpz_com(mx, mx); break;
  case WIZ_W_SHL: if (k >= w) mpz_set_ui(mx, 0); else mpz_mul_2exp(mx, mx, k); break;
  case WIZ_W_SDIV: case WIZ_W_SREM:
    if (mpz_sgn(my) == 0) { if (op == WIZ_W_SDIV) mpz_set_ui(mx, 0); break; }
    wiz_word_signed(mx, w); wiz_word_signed(my, w);
    if (op == WIZ_W_SDIV) mpz_tdiv_q(mx, mx, my); else mpz_tdiv_r(mx, mx, my);
    break;
  case WIZ_W_ASHR: wiz_word_signed(mx, w); mpz_fdiv_q_2exp(mx, mx, k >= w ? w : k); break;
  case WIZ_W_SLT: case WIZ_W_SLE: wiz_word_signed(mx, w); wiz_word_signed(my, w); /* fall through */
  case WIZ_W_EQ: case WIZ_W_ULT: case WIZ_W_ULE: cmp = mpz_cmp(mx, my); break;
  case WIZ_W_AND: mpz_and(mx, mx, my); break;
  case WIZ_W_OR: mpz_ior(mx, mx, my); break;
  case WIZ_W_XOR: mpz_xor(mx, mx, my); break;
  case WIZ_W_LSHR: mpz_fdiv_q_2exp(mx, mx, k); break;
  default: cmp = mpz_tstbit(mx, k) ? 0 : 1; mpz_clear(mx); mpz_clear(my); return WIZ_BOX(cmp == 0);
  }
  mpz_clear(my);
  if (cmp != 2) {
    mpz_clear(mx);
    switch (op) {
    case WIZ_W_EQ: return WIZ_BOX(cmp == 0);
    case WIZ_W_SLT: case WIZ_W_ULT: return WIZ_BOX(cmp < 0);
    default: return WIZ_BOX(cmp <= 0);
    }
  }
  if (w != WIZ_W_ANY) mpz_fdiv_r_2exp(mx, mx, w);
  return wiz_word_of_mpz(mx);
}
#define WIZ_WORD_BIN(name, op) \
  WIZ_API wiz_val wiz_word_##name(uint64_t w, wiz_val a, wiz_val b) { return wiz_word_op(op, w, a, b, 0); }
WIZ_WORD_BIN(add, WIZ_W_ADD)
WIZ_WORD_BIN(sub, WIZ_W_SUB)
WIZ_WORD_BIN(mul, WIZ_W_MUL)
WIZ_WORD_BIN(udiv, WIZ_W_UDIV)
WIZ_WORD_BIN(umod, WIZ_W_UMOD)
WIZ_WORD_BIN(sdiv, WIZ_W_SDIV)
WIZ_WORD_BIN(srem, WIZ_W_SREM)
#define WIZ_WORD_ANY(name, op) \
  WIZ_API wiz_val wiz_word_##name(wiz_val a, wiz_val b) { return wiz_word_op(op, WIZ_W_ANY, a, b, 0); }
WIZ_WORD_ANY(and, WIZ_W_AND)
WIZ_WORD_ANY(or, WIZ_W_OR)
WIZ_WORD_ANY(xor, WIZ_W_XOR)
#define WIZ_WORD_CMP(name, op, w) \
  WIZ_API int wiz_word_##name(uint64_t width, wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(op, w, a, b, 0)) != 0; }
WIZ_WORD_CMP(slt, WIZ_W_SLT, width)
WIZ_WORD_CMP(sle, WIZ_W_SLE, width)
WIZ_API int wiz_word_eq(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(WIZ_W_EQ, WIZ_W_ANY, a, b, 0)) != 0; }
WIZ_API int wiz_word_ult(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(WIZ_W_ULT, WIZ_W_ANY, a, b, 0)) != 0; }
WIZ_API int wiz_word_ule(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(WIZ_W_ULE, WIZ_W_ANY, a, b, 0)) != 0; }
WIZ_API wiz_val wiz_word_not(uint64_t w, wiz_val a) { return wiz_word_op(WIZ_W_NOT, w, a, WIZ_BOX(0), 0); }
WIZ_API wiz_val wiz_word_shl(uint64_t w, wiz_val a, wiz_val k) {
  return wiz_word_op(WIZ_W_SHL, w, a, WIZ_BOX(0), wiz_word_amount(k));
}
WIZ_API wiz_val wiz_word_ashr(uint64_t w, wiz_val a, wiz_val k) {
  return wiz_word_op(WIZ_W_ASHR, w, a, WIZ_BOX(0), wiz_word_amount(k));
}
WIZ_API wiz_val wiz_word_lshr(wiz_val a, wiz_val k) {
  return wiz_word_op(WIZ_W_LSHR, WIZ_W_ANY, a, WIZ_BOX(0), wiz_word_amount(k));
}
WIZ_API int wiz_word_bit(wiz_val a, wiz_val i) {
  return WIZ_UNBOX(wiz_word_op(WIZ_W_BIT, WIZ_W_ANY, a, WIZ_BOX(0), wiz_word_amount(i))) != 0;
}
/* the top bit of a width-w word (the sign of an `IntN w`); Nat.testBit a (w - 1) */
WIZ_API int wiz_word_msb(uint64_t w, wiz_val a) {
  return WIZ_UNBOX(wiz_word_op(WIZ_W_BIT, WIZ_W_ANY, a, WIZ_BOX(0), w ? w - 1 : 0)) != 0;
}
/* n mod 2^w, and (-n) mod 2^w, for a number n (a Nat) */
static wiz_val wiz_word_reduce(uint64_t w, wiz_val n, int neg) {
  if (WIZ_IS_SCALAR(n) && w <= 64) {
    uint64_t x = WIZ_UNBOX(n);
    return wiz_word_out((neg ? (uint64_t)0 - x : x) & wiz_word_mask(w));
  }
  mpz_t z;
  wiz_to_mpz(z, n);
  wiz_dec(n);
  if (neg) mpz_neg(z, z);
  mpz_fdiv_r_2exp(z, z, w);
  return wiz_word_of_mpz(z);
}
WIZ_API wiz_val wiz_word_of_nat(uint64_t w, wiz_val n) { return wiz_word_reduce(w, n, 0); }
WIZ_API wiz_val wiz_word_of_neg(uint64_t w, wiz_val n) { return wiz_word_reduce(w, n, 1); }
/* the same bits at another type (`toIntN`, `toUIntN`) */
WIZ_API wiz_val wiz_word_cast(wiz_val a) { return a; }
/* to width v: zero-extending or truncating */
WIZ_API wiz_val wiz_word_zext(uint64_t v, wiz_val a) {
  uint64_t x;
  if (wiz_word_in(a, &x)) { if (!WIZ_IS_SCALAR(a)) wiz_dec(a); return wiz_word_out(x & wiz_word_mask(v)); }
  mpz_t z;
  wiz_word_mpz(z, a);
  wiz_dec(a);
  mpz_fdiv_r_2exp(z, z, v);
  return wiz_word_of_mpz(z);
}
/* from width w to width v: sign-extending or truncating */
WIZ_API wiz_val wiz_word_sext(uint64_t w, uint64_t v, wiz_val a) {
  uint64_t x;
  if (w <= 64 && v <= 64 && wiz_word_in(a, &x)) {
    int s = w >= 64 ? 0 : 64 - (int)w;
    int64_t sx = w ? (int64_t)(x << s) >> s : 0;
    if (!WIZ_IS_SCALAR(a)) wiz_dec(a);
    return wiz_word_out((uint64_t)sx & wiz_word_mask(v));
  }
  mpz_t z;
  wiz_word_mpz(z, a);
  wiz_dec(a);
  wiz_word_signed(z, w);
  mpz_fdiv_r_2exp(z, z, v);
  return wiz_word_of_mpz(z);
}

/* a constructor value: a flat object ⟨tag f₁ … fₙ⟩, or just the tag without fields */
static wiz_val wiz_con(uint32_t tag, uint32_t n, wiz_val *fields) {
  if (n == 0) return WIZ_BOX(tag);
  wiz_val r = wiz_ctor_new(tag, n);
  for (uint32_t i = 0; i < n; i++) WIZ_SET(r, i, fields[i]);
  return r;
}
static wiz_val wiz_field_ref(wiz_val v, uint32_t i) { /* borrowed */
  return ((wiz_ctor *)v)->fields[i];
}

WIZ_API int wiz_in_bool(wiz_val v) { int b = (int)wiz_tag(v); wiz_dec(v); return b; }
WIZ_API wiz_val wiz_out_bool(int b) { return wiz_con(b ? 1 : 0, 0, NULL); }

/* String := String.mk (List Char), Char := Char.mk Nat; C strings are UTF-8 */
WIZ_API char *wiz_in_string(wiz_val s) {
  size_t cap = 16, len = 0;
  char *buf = (char *)malloc(cap);
  wiz_val l = wiz_field_ref(s, 0);
  while (wiz_tag(l) == 1) {
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

/* foreign pointers: borrowed for a call (the wrapper drops the reference after it) */
WIZ_API void *wiz_in_ptr(wiz_val v) { return ((wiz_ext *)v)->ptr; }
WIZ_API wiz_val wiz_out_ptr(void *p, void (*fin)(void *)) {
  wiz_ext *e = (wiz_ext *)wiz_alloc(sizeof(wiz_ext), WIZ_TAG_EXT, 0);
  e->ptr = p;
  e->fin = fin;
  return (wiz_val)e;
}

/* byte buffers: functional, but updated in place when unique (Perceus) */
WIZ_API wiz_val wiz_bytes_empty(void) {
  wiz_bytes *b = (wiz_bytes *)wiz_alloc(sizeof(wiz_bytes), WIZ_TAG_BYTES, 0);
  b->len = 0; b->cap = 0; b->data = NULL;
  return (wiz_val)b;
}
static wiz_val wiz_bytes_unique(wiz_val v) {
  wiz_bytes *b = (wiz_bytes *)v;
  if (b->h.rc == 1) return v;
  wiz_bytes *c = (wiz_bytes *)wiz_bytes_empty();
  c->len = c->cap = b->len;
  c->data = (unsigned char *)malloc(b->len ? b->len : 1);
  memcpy(c->data, b->data, b->len);
  wiz_dec(v);
  return (wiz_val)c;
}
WIZ_API wiz_val wiz_bytes_push(wiz_val v, uint64_t x) {
  v = wiz_bytes_unique(v);
  wiz_bytes *b = (wiz_bytes *)v;
  if (b->len == b->cap) { b->cap = b->cap ? 2 * b->cap : 8; b->data = (unsigned char *)realloc(b->data, b->cap); }
  b->data[b->len++] = (unsigned char)x;
  return v;
}
WIZ_API uint64_t wiz_bytes_size(wiz_val v) { uint64_t n = ((wiz_bytes *)v)->len; wiz_dec(v); return n; }
WIZ_API uint64_t wiz_bytes_get(wiz_val v, uint64_t i) {
  wiz_bytes *b = (wiz_bytes *)v;
  uint64_t r = i < b->len ? b->data[i] : 0;
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_bytes_of_string(const char *s) {
  wiz_val v = wiz_bytes_empty();
  for (const char *p = s; *p; p++) v = wiz_bytes_push(v, (unsigned char)*p);
  return v;
}
static char *wiz_scratch = NULL;
WIZ_API const char *wiz_bytes_to_string(wiz_val v) {
  wiz_bytes *b = (wiz_bytes *)v;
  free(wiz_scratch);
  wiz_scratch = (char *)malloc(b->len + 1);
  memcpy(wiz_scratch, b->data, b->len);
  wiz_scratch[b->len] = 0;
  wiz_dec(v);
  return wiz_scratch;
}

/* ---- arrays: functional, updated in place when unique ---- */

WIZ_API wiz_val wiz_array_empty(void) {
  wiz_array *a = (wiz_array *)wiz_alloc(sizeof(wiz_array), WIZ_TAG_ARRAY, 0);
  a->len = a->cap = 0; a->data = NULL;
  return (wiz_val)a;
}
static wiz_val wiz_array_unique(wiz_val v) {
  wiz_array *a = (wiz_array *)v;
  if (a->h.rc == 1) return v;
  wiz_array *c = (wiz_array *)wiz_array_empty();
  c->len = c->cap = a->len;
  c->data = (wiz_val *)malloc((a->len ? a->len : 1) * sizeof(wiz_val));
  for (size_t i = 0; i < a->len; i++) { c->data[i] = a->data[i]; wiz_inc(a->data[i]); }
  wiz_dec(v);
  return (wiz_val)c;
}
WIZ_API wiz_val wiz_array_push(wiz_val v, wiz_val x) {
  v = wiz_array_unique(v);
  wiz_array *a = (wiz_array *)v;
  if (a->len == a->cap) { a->cap = a->cap ? 2 * a->cap : 8; a->data = (wiz_val *)realloc(a->data, a->cap * sizeof(wiz_val)); }
  a->data[a->len++] = x;
  return v;
}
WIZ_API uint64_t wiz_array_size(wiz_val v) { uint64_t n = ((wiz_array *)v)->len; wiz_dec(v); return n; }
/* the element at i (a new reference), or the default */
WIZ_API wiz_val wiz_array_get(wiz_val v, uint64_t i, wiz_val dflt) {
  wiz_array *a = (wiz_array *)v;
  wiz_val r;
  if (i < a->len) { r = a->data[i]; wiz_inc(r); wiz_dec(dflt); } else r = dflt;
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_array_set(wiz_val v, uint64_t i, wiz_val x) {
  if (i >= ((wiz_array *)v)->len) { wiz_dec(x); return v; }
  v = wiz_array_unique(v);
  wiz_array *a = (wiz_array *)v;
  wiz_dec(a->data[i]);
  a->data[i] = x;
  return v;
}

/* ---- text ---- */

static wiz_val wiz_str_new(const char *s, size_t n) {
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + n + 1, WIZ_TAG_STR, 0);
  t->len = n;
  memcpy(t->data, s, n);
  t->data[n] = 0;
  return (wiz_val)t;
}
WIZ_API wiz_val wiz_str_of_cstr(const char *s) { return wiz_str_new(s, strlen(s)); }
WIZ_API const char *wiz_str_to_cstr(wiz_val v) {
  wiz_str *t = (wiz_str *)v;
  free(wiz_scratch);
  wiz_scratch = (char *)malloc(t->len + 1);
  memcpy(wiz_scratch, t->data, t->len + 1);
  wiz_dec(v);
  return wiz_scratch;
}
WIZ_API wiz_val wiz_str_append(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + x->len + y->len + 1, WIZ_TAG_STR, 0);
  t->len = x->len + y->len;
  memcpy(t->data, x->data, x->len);
  memcpy(t->data + x->len, y->data, y->len + 1);
  wiz_dec(a); wiz_dec(b);
  return (wiz_val)t;
}
WIZ_API uint64_t wiz_str_size(wiz_val v) { uint64_t n = ((wiz_str *)v)->len; wiz_dec(v); return n; }
WIZ_API uint64_t wiz_str_byte(wiz_val v, uint64_t i) {
  wiz_str *t = (wiz_str *)v;
  uint64_t r = i < t->len ? (unsigned char)t->data[i] : 0;
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_str_slice(wiz_val v, uint64_t from, uint64_t to) {
  wiz_str *t = (wiz_str *)v;
  if (to > t->len) to = t->len;
  if (from > to) from = to;
  wiz_val r = wiz_str_new(t->data + from, to - from);
  wiz_dec(v);
  return r;
}
WIZ_API int wiz_str_eq(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  int r = x->len == y->len && memcmp(x->data, y->data, x->len) == 0;
  wiz_dec(a); wiz_dec(b);
  return r;
}
WIZ_API int wiz_str_lt(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  size_t n = x->len < y->len ? x->len : y->len;
  int c = memcmp(x->data, y->data, n);
  int r = c < 0 || (c == 0 && x->len < y->len);
  wiz_dec(a); wiz_dec(b);
  return r;
}

/* ---- maps from text: functional, updated in place when unique ---- */

static uint64_t wiz_str_hash(wiz_str *t) {
  uint64_t h = 1469598103934665603ULL;
  for (size_t i = 0; i < t->len; i++) { h ^= (unsigned char)t->data[i]; h *= 1099511628211ULL; }
  return h;
}
static int wiz_str_same(wiz_str *x, wiz_str *y) { return x->len == y->len && memcmp(x->data, y->data, x->len) == 0; }
WIZ_API wiz_val wiz_map_empty(void) {
  wiz_map *m = (wiz_map *)wiz_alloc(sizeof(wiz_map), WIZ_TAG_MAP, 0);
  m->count = 0; m->cap = 8;
  m->keys = (wiz_val *)calloc(8, sizeof(wiz_val));
  m->vals = (wiz_val *)calloc(8, sizeof(wiz_val));
  return (wiz_val)m;
}
static wiz_val wiz_map_unique(wiz_val v) {
  wiz_map *m = (wiz_map *)v;
  if (m->h.rc == 1) return v;
  wiz_map *c = (wiz_map *)wiz_alloc(sizeof(wiz_map), WIZ_TAG_MAP, 0);
  c->count = m->count; c->cap = m->cap;
  c->keys = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
  c->vals = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
  for (size_t i = 0; i < m->cap; i++)
    if (m->keys[i]) { c->keys[i] = m->keys[i]; c->vals[i] = m->vals[i]; wiz_inc(m->keys[i]); wiz_inc(m->vals[i]); }
  wiz_dec(v);
  return (wiz_val)c;
}
static void wiz_map_put(wiz_map *m, wiz_val k, wiz_val x) {
  size_t i = wiz_str_hash((wiz_str *)k) & (m->cap - 1);
  while (m->keys[i] && !wiz_str_same((wiz_str *)m->keys[i], (wiz_str *)k)) i = (i + 1) & (m->cap - 1);
  if (m->keys[i]) { wiz_dec(m->keys[i]); wiz_dec(m->vals[i]); } else m->count++;
  m->keys[i] = k; m->vals[i] = x;
}
WIZ_API wiz_val wiz_map_insert(wiz_val v, wiz_val k, wiz_val x) {
  v = wiz_map_unique(v);
  wiz_map *m = (wiz_map *)v;
  if (2 * (m->count + 1) > m->cap) {
    size_t oc = m->cap;
    wiz_val *ok = m->keys, *ov = m->vals;
    m->cap *= 2; m->count = 0;
    m->keys = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
    m->vals = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
    for (size_t i = 0; i < oc; i++) if (ok[i]) wiz_map_put(m, ok[i], ov[i]);
    free(ok); free(ov);
  }
  wiz_map_put(m, k, x);
  return v;
}
/* the value for k (a new reference), or the default */
WIZ_API wiz_val wiz_map_find(wiz_val v, wiz_val k, wiz_val dflt) {
  wiz_map *m = (wiz_map *)v;
  size_t i = wiz_str_hash((wiz_str *)k) & (m->cap - 1);
  wiz_val r = dflt;
  while (m->keys[i]) {
    if (wiz_str_same((wiz_str *)m->keys[i], (wiz_str *)k)) { r = m->vals[i]; wiz_inc(r); wiz_dec(dflt); break; }
    i = (i + 1) & (m->cap - 1);
  }
  wiz_dec(v); wiz_dec(k);
  return r;
}
WIZ_API uint64_t wiz_map_size(wiz_val v) { uint64_t n = ((wiz_map *)v)->count; wiz_dec(v); return n; }

WIZ_API void wiz_io_write_file(const char *path, const char *text) {
  FILE *f = fopen(path, "wb");
  if (f) { fputs(text, f); fclose(f); }
}

/* files, for the library */
WIZ_API const char *wiz_io_read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  free(wiz_scratch);
  wiz_scratch = NULL;
  if (!f) { wiz_scratch = (char *)calloc(1, 1); return wiz_scratch; }
  size_t cap = 1024, len = 0;
  wiz_scratch = (char *)malloc(cap);
  size_t n;
  while ((n = fread(wiz_scratch + len, 1, cap - len - 1, f)) > 0) {
    len += n;
    if (len + 1 == cap) { cap *= 2; wiz_scratch = (char *)realloc(wiz_scratch, cap); }
  }
  wiz_scratch[len] = 0;
  fclose(f);
  return wiz_scratch;
}

/* the program's arguments (without its name), saved by `main` (stage 21k) */
static int wiz_argc;
static char **wiz_argv;
WIZ_API void wiz_set_args(int argc, char **argv) { wiz_argc = argc; wiz_argv = argv; }
WIZ_API uint64_t wiz_io_arg_count(void) { return wiz_argc > 1 ? (uint64_t)(wiz_argc - 1) : 0; }
WIZ_API const char *wiz_io_arg(uint64_t i) { return i + 1 < (uint64_t)wiz_argc ? wiz_argv[i + 1] : ""; }

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
  if (h->tag == WIZ_TAG_CLO || h->tag == WIZ_TAG_THUNK) { printf("<fn>"); return; }
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
  if (wiz_live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)wiz_live); wiz_report_leaks(); return 2; }
  return 0;
}

WIZ_API int wiz_finish(wiz_val r) {
  wiz_print(r);
  putchar('\n');
  wiz_dec(r);
  if (wiz_live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)wiz_live); wiz_report_leaks(); return 2; }
  return 0;
}

/* ---- main: run on a thread with a big stack (deep recursion is normal in functional
   code); $WIZ_STACK_MB sets its size, default 1024 ---- */

typedef struct { wiz_val (*entry)(void); int io; int rc; } wiz_main_args;

static void *wiz_main_thread(void *p) {
  wiz_main_args *a = (wiz_main_args *)p;
  wiz_val v = a->entry();
  a->rc = a->io ? wiz_finish_io(v) : wiz_finish(v);
  return NULL;
}

WIZ_API int wiz_run_main(wiz_val (*entry)(void), int io) {
  wiz_main_args args = {entry, io, 0};
  const char *mb = getenv("WIZ_STACK_MB");
  size_t size = (size_t)(mb ? atol(mb) : 1024) << 20;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, size);
  pthread_t t;
  if (pthread_create(&t, &attr, wiz_main_thread, &args) != 0) return wiz_main_thread(&args), args.rc;
  pthread_join(t, NULL);
  return args.rc;
}
