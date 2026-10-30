/* K.E.N.D.R.A.H. runtime for target T2: wasm32, freestanding (no libc, no WASI). See docs/TARGETS.md.
 * Same ABI as kd_rt.c. Host imports (module "env"): kd_write(fd, ptr, len), kd_f64_to_str(x, buf) -> len,
 * kd_fmod(a, b), kd_exit(code) (does not return). Export: kd_start() -> exit status. Error messages match the
 * native x86-64 runtime byte for byte. */
#include <stdint.h>
#include <stddef.h>

#define IMPORT(n) __attribute__((import_module("env"), import_name(n)))
IMPORT("kd_write") extern void host_write(int32_t fd, const void *p, int32_t n);
IMPORT("kd_f64_to_str") extern int32_t host_f64_to_str(double x, char *buf);
IMPORT("kd_fmod") extern double host_fmod(double a, double b);
IMPORT("kd_exit") extern void host_exit(int32_t code) __attribute__((noreturn));

extern const char kd_src_path[];
extern int kd_entry(void);

double fmod(double a, double b) { return host_fmod(a, b); }

/* 128-bit multiply (compiler-rt builtin, needed by the i64 overflow-checked multiplication on wasm32). */
typedef union { __int128 v; struct { uint64_t lo, hi; } s; } U128;
__int128 __multi3(__int128 a, __int128 b) {
    U128 x, y, r;
    x.v = a; y.v = b;
    uint64_t a0 = x.s.lo & 0xffffffffu, a1 = x.s.lo >> 32, b0 = y.s.lo & 0xffffffffu, b1 = y.s.lo >> 32;
    uint64_t p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
    uint64_t mid = (p00 >> 32) + (p01 & 0xffffffffu) + (p10 & 0xffffffffu);
    r.s.lo = (p00 & 0xffffffffu) | (mid << 32);
    r.s.hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32) + x.s.lo * y.s.hi + x.s.hi * y.s.lo;
    return r.v;
}

/* ---- memory primitives (compiled to bulk-memory instructions) ---- */
void *memcpy(void *d, const void *s, size_t n) { __builtin_memcpy(d, s, n); return d; }
void *memset(void *d, int c, size_t n) { __builtin_memset(d, c, n); return d; }
int memcmp(const void *a, const void *b, size_t n) {
    const unsigned char *x = a, *y = b;
    for (size_t i = 0; i < n; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
    return 0;
}
static size_t cstrlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }

/* ---- buffered stdout, unbuffered stderr ---- */
static char out_buf[1 << 16];
static int32_t out_len = 0;
static void flush_out(void) { if (out_len) { host_write(1, out_buf, out_len); out_len = 0; } }
static void out_bytes(const char *p, int64_t n) {
    for (int64_t i = 0; i < n; i++) {
        if (out_len == (int32_t)sizeof out_buf) flush_out();
        out_buf[out_len++] = p[i];
    }
}
static void out_str(const char *s) { out_bytes(s, (int64_t)cstrlen(s)); }

/* small formatter for error messages (collected, then written to stderr in one call) */
static char err_buf[512];
static int32_t err_len = 0;
static void e_bytes(const char *p, int64_t n) { for (int64_t i = 0; i < n && err_len < (int32_t)sizeof err_buf - 1; i++) err_buf[err_len++] = p[i]; }
static void e_str(const char *s) { e_bytes(s, (int64_t)cstrlen(s)); }
static int fmt_u64(char *b, uint64_t v) {
    char t[24]; int n = 0;
    do { t[n++] = (char)('0' + v % 10); v /= 10; } while (v);
    for (int i = 0; i < n; i++) b[i] = t[n - 1 - i];
    return n;
}
static int fmt_i64(char *b, int64_t v) {
    if (v < 0) { b[0] = '-'; return 1 + fmt_u64(b + 1, (uint64_t)0 - (uint64_t)v); }
    return fmt_u64(b, (uint64_t)v);
}
static void e_int(int64_t v, int is_unsigned) {
    char b[32];
    int n = is_unsigned ? fmt_u64(b, (uint64_t)v) : fmt_i64(b, v);
    e_bytes(b, n);
}
static void e_begin(int32_t line, int32_t col) {
    err_len = 0;
    e_str(kd_src_path); e_str(":"); e_int(line, 0); e_str(":"); e_int(col, 0); e_str(": runtime error: ");
}
static void e_end(void) __attribute__((noreturn));
static void e_end(void) {
    flush_out();
    host_write(2, err_buf, err_len);
    host_exit(2);
}

void kd_fail(int32_t line, int32_t col, const char *msg, int64_t len) { e_begin(line, col); e_bytes(msg, len); e_str("\n"); e_end(); }
void kd_oob(int32_t line, int32_t col, int64_t idx, int32_t idx_unsigned, int64_t len) {
    e_begin(line, col); e_str("array index out of bounds: the index is "); e_int(idx, idx_unsigned);
    e_str(" but the length is "); e_int(len, 0); e_str("\n"); e_end();
}
void kd_shift_fail(int32_t line, int32_t col, int64_t amt, int32_t amt_unsigned, const char *ty, int64_t tylen, int32_t bits) {
    e_begin(line, col); e_str("shift amount "); e_int(amt, amt_unsigned); e_str(" out of range for "); e_bytes(ty, tylen);
    e_str(" (valid: 0.."); e_int(bits, 0); e_str(")\n"); e_end();
}
void kd_mem_oob(int32_t line, int32_t col, int64_t addr, int32_t addr_unsigned, int64_t size) {
    e_begin(line, col); e_str("memory access out of bounds: address "); e_int(addr, addr_unsigned);
    e_str(" (valid: 0.."); e_int(size, 0); e_str(")\n"); e_end();
}
void kd_poke_fail(int32_t line, int32_t col, int64_t v, int32_t v_unsigned) {
    e_begin(line, col); e_str("poke value "); e_int(v, v_unsigned); e_str(" does not fit in a byte\n"); e_end();
}

void kd_print_i64(int64_t v) { char b[32]; int n = fmt_i64(b, v); b[n++] = '\n'; out_bytes(b, n); }
void kd_print_u64(int64_t v) { char b[32]; int n = fmt_u64(b, (uint64_t)v); b[n++] = '\n'; out_bytes(b, n); }
void kd_print_bool(int32_t b) { out_str(b ? "true\n" : "false\n"); }
void kd_print_str(const char *p, int64_t n) { out_bytes(p, n); out_bytes("\n", 1); }
int32_t kd_str_eq(const char *a, int64_t an, const char *b, int64_t bn) { return an == bn && (an == 0 || memcmp(a, b, (size_t)an) == 0); }
void kd_print_f64(double x) { char b[400]; int32_t n = host_f64_to_str(x, b); b[n++] = '\n'; out_bytes(b, n); }

/* ---- allocator: first-fit free list over linear memory (grows with memory.grow) ---- */
extern unsigned char __heap_base;
typedef struct Blk { size_t size; struct Blk *next; } Blk; /* header precedes the payload; `next` used while free */
static Blk *free_list = NULL;
static unsigned char *heap_top = NULL, *heap_end = NULL;

static void *raw_alloc(size_t n) {
    n = (n + 15) & ~(size_t)15;
    Blk **pp = &free_list;
    for (Blk *b = free_list; b; pp = &b->next, b = b->next) {
        if (b->size >= n) { *pp = b->next; return (unsigned char *)b + 16; }
    }
    if (!heap_top) {
        heap_top = (unsigned char *)(((size_t)&__heap_base + 15) & ~(size_t)15);
        heap_end = (unsigned char *)(__builtin_wasm_memory_size(0) * 65536u);
    }
    size_t need = n + 16;
    if (heap_top + need > heap_end) {
        size_t pages = (need + 65535) / 65536;
        if (__builtin_wasm_memory_grow(0, pages) == (size_t)-1) return NULL;
        heap_end = (unsigned char *)(__builtin_wasm_memory_size(0) * 65536u);
        if (heap_top + need > heap_end) return NULL;
    }
    Blk *b = (Blk *)heap_top;
    heap_top += need;
    b->size = n;
    return (unsigned char *)b + 16;
}
static void raw_free(void *p) {
    if (!p) return;
    Blk *b = (Blk *)((unsigned char *)p - 16);
    b->next = free_list;
    free_list = b;
}

static int64_t kd_live = 0;
static void *xmalloc(int32_t line, int32_t col, size_t n) {
    void *p = raw_alloc(n ? n : 1);
    if (!p) kd_fail(line, col, "out of memory", 13);
    return p;
}

/* ---- owned strings (docs/MEMORY.md section 3) ---- */
typedef struct { char *data; int64_t len, cap; } KdString;
static KdString *mk(int32_t line, int32_t col, const char *a, int64_t an, const char *b, int64_t bn) {
    KdString *s = xmalloc(line, col, sizeof *s);
    s->len = an + bn;
    s->cap = s->len;
    s->data = xmalloc(line, col, (size_t)s->cap);
    if (an) memcpy(s->data, a, (size_t)an);
    if (bn) memcpy(s->data + an, b, (size_t)bn);
    kd_live++;
    return s;
}
KdString *kd_string_from(int32_t line, int32_t col, const char *p, int64_t n) { return mk(line, col, p, n, NULL, 0); }
KdString *kd_string_concat(int32_t line, int32_t col, KdString **a, KdString **b) { return mk(line, col, (*a)->data, (*a)->len, (*b)->data, (*b)->len); }
KdString *kd_string_clone(int32_t line, int32_t col, KdString **a) { return mk(line, col, (*a)->data, (*a)->len, NULL, 0); }
void kd_string_push(int32_t line, int32_t col, KdString **sp, const char *p, int64_t n) {
    KdString *s = *sp;
    if (s->len + n > s->cap) {
        int64_t nc = s->cap * 2 > s->len + n ? s->cap * 2 : s->len + n;
        char *nd = xmalloc(line, col, (size_t)nc);
        if (s->len) memcpy(nd, s->data, (size_t)s->len);
        raw_free(s->data);
        s->data = nd;
        s->cap = nc;
    }
    if (n) memcpy(s->data + s->len, p, (size_t)n);
    s->len += n;
}
int64_t kd_string_len(KdString **s) { return (*s)->len; }
int32_t kd_string_eq(KdString **a, KdString **b) { return (*a)->len == (*b)->len && ((*a)->len == 0 || memcmp((*a)->data, (*b)->data, (size_t)(*a)->len) == 0); }
void kd_print_string(KdString **s) { out_bytes((*s)->data, (*s)->len); out_bytes("\n", 1); }
void kd_string_drop(KdString *s) {
    if (!s) return;
    raw_free(s->data);
    raw_free(s);
    kd_live--;
}

/* ---- owned vectors of scalars (docs/MEMORY.md section 3b) ---- */
typedef struct { char *data; int64_t len, cap, esz; } KdVec;
KdVec *kd_vec_new(int32_t line, int32_t col, int64_t esz) {
    KdVec *v = xmalloc(line, col, sizeof *v);
    v->data = NULL; v->len = 0; v->cap = 0; v->esz = esz;
    kd_live++;
    return v;
}
void *kd_vec_push(int32_t line, int32_t col, KdVec **vp) {
    KdVec *v = *vp;
    if (v->len == v->cap) {
        int64_t nc = v->cap ? v->cap * 2 : 4;
        char *nd = xmalloc(line, col, (size_t)(nc * v->esz));
        if (v->len) memcpy(nd, v->data, (size_t)(v->len * v->esz));
        raw_free(v->data);
        v->data = nd;
        v->cap = nc;
    }
    return v->data + (v->len++) * v->esz;
}
int64_t kd_vec_len(KdVec **vp) { return (*vp)->len; }
void *kd_vec_at(int32_t line, int32_t col, KdVec **vp, int64_t idx, int32_t idx_unsigned) {
    KdVec *v = *vp;
    int bad = idx_unsigned ? (uint64_t)idx >= (uint64_t)v->len : (idx < 0 || idx >= v->len);
    if (bad) {
        e_begin(line, col); e_str("vector index out of bounds: the index is "); e_int(idx, idx_unsigned);
        e_str(" but the length is "); e_int(v->len, 0); e_str("\n"); e_end();
    }
    return v->data + idx * v->esz;
}
void *kd_vec_pop(int32_t line, int32_t col, KdVec **vp) {
    KdVec *v = *vp;
    if (v->len == 0) kd_fail(line, col, "pop from an empty Vec", 21);
    return v->data + (--v->len) * v->esz;
}
KdVec *kd_vec_clone(int32_t line, int32_t col, KdVec **vp) {
    KdVec *v = *vp;
    KdVec *c = kd_vec_new(line, col, v->esz);
    if (v->len) {
        c->data = xmalloc(line, col, (size_t)(v->len * v->esz));
        memcpy(c->data, v->data, (size_t)(v->len * v->esz));
        c->len = c->cap = v->len;
    }
    return c;
}
void kd_vec_drop(KdVec *v) {
    if (!v) return;
    raw_free(v->data);
    raw_free(v);
    kd_live--;
}

/* ---- owned heap cells, `Box<T>` (docs/MEMORY.md section 3d). The compiler stores/loads the contents itself and
 * runs the contents' drop glue before calling kd_box_free. */
void *kd_box_new(int32_t line, int32_t col, int64_t sz) { void *p = xmalloc(line, col, (size_t)sz); kd_live++; return p; }
void kd_box_free(void *p) { if (!p) return; raw_free(p); kd_live--; }

__attribute__((export_name("kd_start"))) int32_t kd_start(void) {
    int rc = kd_entry();
    flush_out();
    if (rc == 0 && kd_live != 0) {
        err_len = 0;
        e_str("internal error: memory leak: "); e_int(kd_live, 0); e_str(" owned allocation(s) were not freed\n");
        host_write(2, err_buf, err_len);
        return 70;
    }
    return rc;
}
