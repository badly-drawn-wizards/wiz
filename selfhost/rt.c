/* The runtime of the self-hosted backend (stage 21b): what `Backend.wiz` generates
   `#include`s this. A minimal one: memory is garbage collected (Boehm), values are
   tagged words. A scalar (`BOX(n)`, low bit 1) is a number, a tag, or `◾`; anything
   else points to an object: a constructor (a tag and fields; payloads are nested
   pairs, `⟨0 a b⟩`), a closure, a string (`Str`), an array or a map. */

#include <stddef.h>
#include <gc.h>
#include <sys/resource.h>
#include <unistd.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <alloca.h>

typedef uintptr_t V;
#define BOX(n) ((((V)(n)) << 1) | 1)
#define ISBOX(v) (((v) & 1) != 0)
#define UNBOX(v) ((v) >> 1)

enum { T_CLO = 0x7fff0000u, T_STR, T_ARR, T_MAP, T_HYP };

typedef struct { uint32_t tag, n; V f[]; } Obj;
typedef V (*Fn)(V *env, V a);
typedef struct { uint32_t tag, n; Fn fn; V env[]; } Clo;

static V unreach(void) { fprintf(stderr, "wiz: unreachable\n"); exit(3); }
static void die(const char *m) { fprintf(stderr, "wiz: %s\n", m); exit(3); }

static V mkobj(uint32_t t, uint32_t n, V *fs) {
  Obj *o = (Obj *)GC_MALLOC(sizeof(Obj) + n * sizeof(V));
  if (!o) die("out of memory");
  o->tag = t; o->n = n;
  memcpy(o->f, fs, n * sizeof(V));
  return (V)o;
}
static V mkclo(Fn fn, uint32_t n, V *env) {
  Clo *c = (Clo *)GC_MALLOC(sizeof(Clo) + n * sizeof(V));
  if (!c) die("out of memory");
  c->tag = T_CLO; c->n = n; c->fn = fn;
  if (n) memcpy(c->env, env, n * sizeof(V));
  return (V)c;
}
static V ap(V f, V a) {
  if (ISBOX(f) || ((Clo *)f)->tag != T_CLO) die("applying a non-function");
  Clo *c = (Clo *)f;
  return c->fn(c->env, a);
}
/* a field (of `◾`, an erased payload, `◾` again). A hypothesis of `ind` (`T_HYP`:
   `[suspension, rest, done]`) is computed when its field is first read. */
static V fld(V o, int i) {
  if (ISBOX(o)) return BOX(0);
  Obj *p = (Obj *)o;
  if (p->tag == T_HYP && i == 0) {
    if (p->f[2] == BOX(0)) { p->f[0] = ((Clo *)p->f[0])->fn(((Clo *)p->f[0])->env, BOX(0)); p->f[2] = BOX(1); }
    return p->f[0];
  }
  return (uint32_t)i < p->n ? p->f[i] : BOX(0);
}
static uint32_t tagof(V v) { return ISBOX(v) ? (uint32_t)UNBOX(v) : ((Obj *)v)->tag; }
static V pair(V a, V b) { V fs[2] = {a, b}; return mkobj(0, 2, fs); }

/* ---- data the natives build: Bool, Prod, List, Char, String ---- */

static V boolv(int b) { return pair(BOX(b ? 1 : 0), BOX(0)); }
/* `Prod.mk a b`: the payload `(tag 0, (a, (b, ◾)))` */
static V prodv(V a, V b) { return pair(BOX(0), pair(a, pair(b, BOX(0)))); }
static V nilv(void) { return pair(BOX(0), BOX(0)); }
static V consv(V h, V t) { return pair(BOX(1), pair(h, pair(t, BOX(0)))); }
static V charv(uint32_t c) { return pair(BOX(0), pair(BOX(c), BOX(0))); }
static V stringv(V list) { return pair(BOX(0), pair(list, BOX(0))); }

/* a Wiz string as UTF-8 (a new buffer) */
static char *cstr(V s) {
  size_t cap = 64, len = 0;
  char *buf = (char *)GC_MALLOC_ATOMIC(cap);
  V l = fld(fld(s, 1), 0);
  while (tagof(fld(l, 0)) == 1) {
    V rest = fld(l, 1);
    uint32_t c = (uint32_t)UNBOX(fld(fld(fld(rest, 0), 1), 0));
    if (len + 5 > cap) { char *nb = (char *)GC_MALLOC_ATOMIC(cap * 2); memcpy(nb, buf, len); buf = nb; cap *= 2; }
    if (c < 0x80) buf[len++] = (char)c;
    else if (c < 0x800) { buf[len++] = (char)(0xC0 | (c >> 6)); buf[len++] = (char)(0x80 | (c & 0x3F)); }
    else if (c < 0x10000) { buf[len++] = (char)(0xE0 | (c >> 12)); buf[len++] = (char)(0x80 | ((c >> 6) & 0x3F)); buf[len++] = (char)(0x80 | (c & 0x3F)); }
    else { buf[len++] = (char)(0xF0 | (c >> 18)); buf[len++] = (char)(0x80 | ((c >> 12) & 0x3F)); buf[len++] = (char)(0x80 | ((c >> 6) & 0x3F)); buf[len++] = (char)(0x80 | (c & 0x3F)); }
    l = fld(fld(rest, 1), 0);
  }
  buf[len] = 0;
  return buf;
}
/* UTF-8 text as a Wiz string */
static V wstr(const char *s, size_t n) {
  /* decode to code points, then build the list from the end */
  uint32_t *cps = (uint32_t *)GC_MALLOC_ATOMIC((n + 1) * sizeof(uint32_t));
  size_t k = 0;
  for (size_t i = 0; i < n;) {
    unsigned char b = (unsigned char)s[i];
    uint32_t c; int extra;
    if (b < 0x80) { c = b; extra = 0; } else if (b < 0xE0) { c = b & 0x1F; extra = 1; }
    else if (b < 0xF0) { c = b & 0x0F; extra = 2; } else { c = b & 0x07; extra = 3; }
    i++;
    for (int e = 0; e < extra && i < n; e++, i++) c = (c << 6) | ((unsigned char)s[i] & 0x3F);
    cps[k++] = c;
  }
  V l = nilv();
  while (k > 0) l = consv(charv(cps[--k]), l);
  return stringv(l);
}

/* a string literal from its code points */
static V wcodes(const uint32_t *cps, size_t k) {
  V l = nilv();
  while (k > 0) l = consv(charv(cps[--k]), l);
  return stringv(l);
}

/* ---- primitives the erased code uses ---- */

static V p_unreachable(void) { return unreach(); }
static V p_natSucc(V n) { return BOX(UNBOX(n) + 1); }
/* a number's payload for a match: `(tag 0, ◾)` or `(tag 1, (n - 1, ◾))` */
static V p_natUnpack(V n) {
  uintptr_t k = UNBOX(n);
  return k == 0 ? pair(BOX(0), BOX(0)) : pair(BOX(1), pair(BOX(k - 1), BOX(0)));
}
static V p_natPack(V p) {
  return tagof(fld(p, 0)) == 0 ? BOX(0) : BOX(UNBOX(fld(fld(p, 1), 0)) + 1);
}

/* `ind D m i x`: `m i payload hyps`, the hypotheses computed by walking the description
   (`⟨0 i⟩` ret, `⟨1 ◾ F⟩` arg, `⟨2 j E⟩` rec, `⟨3 ◾ j E⟩` hrec) along the payload */
static V apn(V f, uint32_t n, V *args);
static V p_ind(V nat, V D, V m, V i, V x);
static V hrecFn(V *env, V h) { return p_ind(env[0], env[1], env[2], ap(env[3], h), ap(env[4], h)); }
/* the hypothesis of a recursive field, suspended: `p_ind … j y` when first read (eager
   hypotheses made every structural function walk its whole argument) */
static V recFn(V *env, V u) { (void)u; return p_ind(env[0], env[1], env[2], env[3], env[4]); }
static V lazyHyp(V nat, V D, V m, V j, V y, V rest) {
  V env[5] = {nat, D, m, j, y};
  V fs[3] = {mkclo(recFn, 5, env), rest, BOX(0)};
  return mkobj(T_HYP, 3, fs);
}
static V hyps(V nat, V D, V m, V d, V pl) {
  switch (tagof(d)) {
  case 1: return hyps(nat, D, m, ap(fld(d, 1), fld(pl, 0)), fld(pl, 1));
  case 2: return lazyHyp(nat, D, m, fld(d, 0), fld(pl, 0), hyps(nat, D, m, fld(d, 1), fld(pl, 1)));
  case 3: { V env[5] = {nat, D, m, fld(d, 1), fld(pl, 0)};
    return pair(mkclo(hrecFn, 5, env), hyps(nat, D, m, fld(d, 2), fld(pl, 1))); }
  default: return BOX(0);
  }
}
static V p_ind(V nat, V D, V m, V i, V x) {
  V pl = UNBOX(nat) ? p_natUnpack(x) : x;
  V args[3] = {i, pl, hyps(nat, D, m, D, pl)};
  return apn(m, 3, args);
}

/* ---- natives: curried functions of `n` arguments ---- */

typedef V (*NF)(V *args);
/* env: [the function, its arity, the arguments so far…] */
static V accFn(V *env, V a) {
  uintptr_t arity = UNBOX(env[1]);
  Clo *self = (Clo *)((char *)env - offsetof(Clo, env));
  uint32_t have = self->n - 2;
  V *args = (V *)alloca((have + 1) * sizeof(V));
  memcpy(args, env + 2, have * sizeof(V));
  args[have] = a;
  if (have + 1 == arity) return ((NF)env[0])(args);
  V *nenv = (V *)alloca((have + 3) * sizeof(V));
  nenv[0] = env[0]; nenv[1] = env[1];
  memcpy(nenv + 2, args, (have + 1) * sizeof(V));
  return mkclo(accFn, have + 3, nenv);
}
static V native(NF f, int arity) { V env[2] = {(V)f, BOX(arity)}; return mkclo(accFn, 2, env); }
/* a function of `arity` arguments (captured variables first), `n` of them given */
static V mkfun(NF f, uint32_t arity, uint32_t n, V *args) {
  V *env = (V *)alloca((n + 2) * sizeof(V));
  env[0] = (V)f; env[1] = BOX(arity);
  if (n) memcpy(env + 2, args, n * sizeof(V));
  return mkclo(accFn, n + 2, env);
}
/* `f a₁ … aₙ`: a function that wants that many (or fewer) is called once, without the
   closures of the partial applications in between */
static V apn(V f, uint32_t n, V *args) {
  uint32_t i = 0;
  while (i < n) {
    if (!ISBOX(f) && ((Clo *)f)->tag == T_CLO && ((Clo *)f)->fn == accFn) {
      Clo *c = (Clo *)f;
      uint32_t have = c->n - 2, ar = (uint32_t)UNBOX(c->env[1]), rem = ar - have;
      if (n - i >= rem) {
        V *full = (V *)alloca(ar * sizeof(V));
        memcpy(full, c->env + 2, have * sizeof(V));
        memcpy(full + have, args + i, rem * sizeof(V));
        f = ((NF)c->env[0])(full);
        i += rem;
      } else {
        V *nenv = (V *)alloca((have + (n - i) + 2) * sizeof(V));
        memcpy(nenv, c->env, (have + 2) * sizeof(V));
        memcpy(nenv + 2 + have, args + i, (n - i) * sizeof(V));
        return mkclo(accFn, have + (n - i) + 2, nenv);
      }
    } else { f = ap(f, args[i]); i++; }
  }
  return f;
}
#define NATIVE(name, arity, ...) \
  static V nf_##name(V *a) { __VA_ARGS__ } \
  V get_##name(void) { static V c = 0; if (!c) c = native(nf_##name, arity); return c; }

V get_Nat_46_zero(void) { return BOX(0); }
NATIVE(Nat_46_succ, 1, return BOX(UNBOX(a[0]) + 1);)
NATIVE(Nat_46_pred, 1, return UNBOX(a[0]) ? BOX(UNBOX(a[0]) - 1) : BOX(0);)
NATIVE(Nat_46_add, 2, return BOX(UNBOX(a[0]) + UNBOX(a[1]));)
NATIVE(Nat_46_sub, 2, return UNBOX(a[0]) > UNBOX(a[1]) ? BOX(UNBOX(a[0]) - UNBOX(a[1])) : BOX(0);)
NATIVE(Nat_46_mul, 2, return BOX(UNBOX(a[0]) * UNBOX(a[1]));)
NATIVE(Nat_46_beq, 2, return boolv(UNBOX(a[0]) == UNBOX(a[1]));)
NATIVE(Nat_46_blt, 2, return boolv(UNBOX(a[0]) < UNBOX(a[1]));)
NATIVE(Nat_46_lt, 2, return boolv(UNBOX(a[0]) < UNBOX(a[1]));)
NATIVE(Nat_46_le, 2, return boolv(UNBOX(a[0]) <= UNBOX(a[1]));)
NATIVE(Nat_46_toString, 1, char b[32]; int n = snprintf(b, sizeof b, "%lu", (unsigned long)UNBOX(a[0])); return wstr(b, (size_t)n);)
/* IO: `String → World → Prod Unit World` */
NATIVE(IO_46_println, 2, puts(cstr(a[0])); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_print, 2, fputs(cstr(a[0]), stdout); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_readFile, 2,
  FILE *f = fopen(cstr(a[0]), "rb");
  if (!f) return prodv(wstr("", 0), a[1]);
  size_t cap = 4096, len = 0; char *buf = (char *)GC_MALLOC_ATOMIC(cap);
  for (size_t r; (r = fread(buf + len, 1, cap - len, f)) > 0;) {
    len += r;
    if (len == cap) { char *nb = (char *)GC_MALLOC_ATOMIC(cap * 2); memcpy(nb, buf, len); buf = nb; cap *= 2; }
  }
  fclose(f);
  return prodv(wstr(buf, len), a[1]);)

/* `memo f`: a suspension computed at most once (the kernel's glued values rely on it) */
static V memoFn(V *env, V u) {
  V *cell = (V *)env[1];
  if (!cell[0]) cell[0] = ap(env[0], u);
  return cell[0];
}
/* (the backend's suspended `let`s) */
static V p_memo(V f) { V *cell = (V *)GC_MALLOC(sizeof(V)); cell[0] = 0; V env[2] = {f, (V)cell}; return mkclo(memoFn, 2, env); }
NATIVE(memo, 2, V *cell = (V *)GC_MALLOC(sizeof(V)); cell[0] = 0; V env[2] = {a[1], (V)cell}; return mkclo(memoFn, 2, env);)

/* `Str`: immutable text */
typedef struct { uint32_t tag, n; char s[]; } Str;
static V mkstr(const char *s) {
  size_t n = strlen(s);
  Str *t = (Str *)GC_MALLOC_ATOMIC(sizeof(Str) + n + 1);
  t->tag = T_STR; t->n = (uint32_t)n;
  memcpy(t->s, s, n + 1);
  return (V)t;
}
NATIVE(Str_46_ofString, 1, return mkstr(cstr(a[0]));)

/* Arrays: persistent, Baker's trick. The newest version holds the vector; an older one
   is a difference from a newer one, and is made the holder again when it is used. */
typedef struct Arr {
  uint32_t tag, kind; /* 0: holds the vector; 1: `next` with element `idx` set to `val`;
                         2: `next` cut to length `idx`; 3: `next` extended by `saved` */
  V *data; size_t len, cap;
  size_t idx; V val; struct Arr *next;
  V *saved; size_t nsaved;
} Arr;
static Arr *arrNode(void) { Arr *a = (Arr *)GC_MALLOC(sizeof(Arr)); a->tag = T_ARR; return a; }
/* make `a` hold the vector, turning the holder into the inverse difference */
static void reroot(Arr *a) {
  if (a->kind == 0) return;
  reroot(a->next);
  Arr *n = a->next;
  if (a->kind == 1) {
    V old = n->data[a->idx];
    n->data[a->idx] = a->val;
    n->kind = 1; n->idx = a->idx; n->val = old;
    a->len = n->len;
  } else if (a->kind == 2) {
    size_t k = n->len - a->idx;
    V *sv = (V *)GC_MALLOC(k * sizeof(V) + sizeof(V));
    memcpy(sv, n->data + a->idx, k * sizeof(V));
    n->kind = 3; n->saved = sv; n->nsaved = k;
    a->len = a->idx;
  } else {
    size_t need = n->len + a->nsaved;
    if (need > n->cap) {
      size_t cap = n->cap ? n->cap : 8;
      while (cap < need) cap *= 2;
      V *nd = (V *)GC_MALLOC(cap * sizeof(V));
      memcpy(nd, n->data, n->len * sizeof(V));
      n->data = nd; n->cap = cap;
    }
    memcpy(n->data + n->len, a->saved, a->nsaved * sizeof(V));
    n->kind = 2; n->idx = n->len;
    a->len = need;
  }
  a->data = n->data; a->cap = n->cap; a->kind = 0;
  n->next = a;
}
static Arr *arrAt(V v) { Arr *a = (Arr *)v; reroot(a); return a; }
NATIVE(Array_46_empty, 1, Arr *r = arrNode(); r->kind = 0; return (V)r;)
NATIVE(Array_46_size, 2, return BOX(arrAt(a[1])->len);)
NATIVE(Array_46_getD, 4, Arr *r = arrAt(a[1]); uintptr_t i = UNBOX(a[2]); return i < r->len ? r->data[i] : a[3];)
NATIVE(Array_46_push, 3,
  Arr *r = arrAt(a[1]);
  if (r->len == r->cap) {
    size_t cap = r->cap ? 2 * r->cap : 8;
    V *nd = (V *)GC_MALLOC(cap * sizeof(V));
    memcpy(nd, r->data, r->len * sizeof(V));
    r->data = nd; r->cap = cap;
  }
  r->data[r->len] = a[2];
  Arr *n = arrNode(); n->kind = 0; n->data = r->data; n->len = r->len + 1; n->cap = r->cap;
  r->kind = 2; r->idx = r->len; r->next = n;
  return (V)n;)
NATIVE(Array_46_set, 4,
  Arr *r = arrAt(a[1]); uintptr_t i = UNBOX(a[2]);
  if (i >= r->len) return a[1];
  V old = r->data[i];
  r->data[i] = a[3];
  Arr *n = arrNode(); n->kind = 0; n->data = r->data; n->len = r->len; n->cap = r->cap;
  r->kind = 1; r->idx = i; r->val = old; r->next = n;
  return (V)n;)

/* StrMap: a persistent treap on the keys' text (priorities from a hash) */
typedef struct Node { uint32_t tag, pri; const char *key; V val; struct Node *l, *r; } Node;
static uint32_t hashs(const char *s) { uint32_t h = 2166136261u; for (; *s; s++) h = (h ^ (unsigned char)*s) * 16777619u; return h; }
static Node *mk(const char *k, uint32_t p, V v, Node *l, Node *r) {
  Node *n = (Node *)GC_MALLOC(sizeof(Node));
  n->tag = T_MAP; n->pri = p; n->key = k; n->val = v; n->l = l; n->r = r;
  return n;
}
static Node *rotR(Node *n) { Node *l = n->l; return mk(l->key, l->pri, l->val, l->l, mk(n->key, n->pri, n->val, l->r, n->r)); }
static Node *rotL(Node *n) { Node *r = n->r; return mk(r->key, r->pri, r->val, mk(n->key, n->pri, n->val, n->l, r->l), r->r); }
static Node *ins(Node *n, const char *k, uint32_t p, V v) {
  if (!n) return mk(k, p, v, NULL, NULL);
  int c = strcmp(k, n->key);
  if (c == 0) return mk(n->key, n->pri, v, n->l, n->r);
  if (c < 0) { Node *m = mk(n->key, n->pri, n->val, ins(n->l, k, p, v), n->r); return m->l->pri > m->pri ? rotR(m) : m; }
  Node *m = mk(n->key, n->pri, n->val, n->l, ins(n->r, k, p, v));
  return m->r->pri > m->pri ? rotL(m) : m;
}
static size_t count(Node *n) { return n ? 1 + count(n->l) + count(n->r) : 0; }
/* a map is `◾` (empty) or a node */
static Node *mapOf(V v) { return ISBOX(v) ? NULL : (Node *)v; }
NATIVE(StrMap_46_empty, 1, return BOX(0);)
NATIVE(StrMap_46_insert, 4, const char *k = ((Str *)a[2])->s; return (V)ins(mapOf(a[1]), k, hashs(k), a[3]);)
NATIVE(StrMap_46_findD, 4,
  const char *k = ((Str *)a[2])->s;
  for (Node *n = mapOf(a[1]); n;) { int c = strcmp(k, n->key); if (c == 0) return n->val; n = c < 0 ? n->l : n->r; }
  return a[3];)
NATIVE(StrMap_46_size, 2, return BOX(count(mapOf(a[1])));)

/* the program needs a big stack (deep recursion): raise the limit and start again (a
   thread with a big stack would do, but the collector's stopping of the world lost
   its signals) */
static void rt_start(char **argv) {
  struct rlimit r;
  rlim_t want = (rlim_t)8 << 30;
  if (getrlimit(RLIMIT_STACK, &r) == 0 && r.rlim_cur != RLIM_INFINITY && r.rlim_cur < want && !getenv("WIZ_STACK_SET")) {
    r.rlim_cur = (r.rlim_max == RLIM_INFINITY || r.rlim_max >= want) ? want : r.rlim_max;
    if (setrlimit(RLIMIT_STACK, &r) == 0) { setenv("WIZ_STACK_SET", "1", 1); execv("/proc/self/exe", argv); }
  }
  GC_INIT();
}
