/* K.E.N.D.R.A.H. native runtime for x86-64 Linux (see docs/TARGETS.md).
 * Linked with every compiled program. All error messages match the interpreters byte for byte. */
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern const char kd_src_path[]; /* emitted by the compiler */
extern int kd_entry(void);       /* emitted by the compiler: calls the program's main */

static void die_prefix(int32_t line, int32_t col) {
    fflush(stdout);
    fprintf(stderr, "%s:%d:%d: runtime error: ", kd_src_path, (int)line, (int)col);
}

void kd_fail(int32_t line, int32_t col, const char *msg, int64_t len) {
    die_prefix(line, col);
    fprintf(stderr, "%.*s\n", (int)len, msg);
    exit(2);
}

static void put_int(int64_t v, int is_unsigned) {
    if (is_unsigned) fprintf(stderr, "%llu", (unsigned long long)v);
    else fprintf(stderr, "%lld", (long long)v);
}

void kd_oob(int32_t line, int32_t col, int64_t idx, int32_t idx_unsigned, int64_t len) {
    die_prefix(line, col);
    fputs("array index out of bounds: the index is ", stderr);
    put_int(idx, idx_unsigned);
    fprintf(stderr, " but the length is %lld\n", (long long)len);
    exit(2);
}

void kd_shift_fail(int32_t line, int32_t col, int64_t amt, int32_t amt_unsigned, const char *ty, int64_t tylen, int32_t bits) {
    die_prefix(line, col);
    fputs("shift amount ", stderr);
    put_int(amt, amt_unsigned);
    fprintf(stderr, " out of range for %.*s (valid: 0..%d)\n", (int)tylen, ty, (int)bits);
    exit(2);
}

void kd_mem_oob(int32_t line, int32_t col, int64_t addr, int32_t addr_unsigned, int64_t size) {
    die_prefix(line, col);
    fputs("memory access out of bounds: address ", stderr);
    put_int(addr, addr_unsigned);
    fprintf(stderr, " (valid: 0..%lld)\n", (long long)size);
    exit(2);
}

void kd_poke_fail(int32_t line, int32_t col, int64_t v, int32_t v_unsigned) {
    die_prefix(line, col);
    fputs("poke value ", stderr);
    put_int(v, v_unsigned);
    fputs(" does not fit in a byte\n", stderr);
    exit(2);
}

void kd_print_i64(int64_t v) { printf("%lld\n", (long long)v); }
void kd_print_u64(int64_t v) { printf("%llu\n", (unsigned long long)v); }
void kd_print_bool(int32_t b) { fputs(b ? "true\n" : "false\n", stdout); }
void kd_print_str(const char *p, int64_t n) { fwrite(p, 1, (size_t)n, stdout); fputc('\n', stdout); }

int32_t kd_str_eq(const char *a, int64_t an, const char *b, int64_t bn) {
    return an == bn && (an == 0 || memcmp(a, b, (size_t)an) == 0);
}

/* Rust `{:?}` formatting of f64: shortest round-trip digits; exponential form iff abs >= 1e16 or abs < 1e-4. */
void kd_print_f64(double x) {
    char out[400];
    if (isnan(x)) { puts("NaN"); return; }
    if (isinf(x)) { puts(x < 0 ? "-inf" : "inf"); return; }
    if (x == 0) { puts(signbit(x) ? "-0.0" : "0.0"); return; }
    char t[64];
    for (int p = 0; p <= 17; p++) {
        snprintf(t, sizeof t, "%.*e", p, x);
        if (strtod(t, NULL) == x) break;
    }
    const char *s = t;
    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    char digits[32];
    int n = 0;
    while (*s && *s != 'e') { if (*s != '.') digits[n++] = *s; s++; }
    int e = atoi(s + 1);
    while (n > 1 && digits[n - 1] == '0') n--;
    char *o = out;
    if (neg) *o++ = '-';
    double ax = fabs(x);
    if (ax >= 1e16 || ax < 1e-4) {
        *o++ = digits[0];
        if (n > 1) { *o++ = '.'; memcpy(o, digits + 1, (size_t)(n - 1)); o += n - 1; }
        o += sprintf(o, "e%d", e);
    } else if (e >= 0) {
        for (int i = 0; i <= e; i++) *o++ = i < n ? digits[i] : '0';
        *o++ = '.';
        if (n > e + 1) { memcpy(o, digits + e + 1, (size_t)(n - e - 1)); o += n - e - 1; }
        else *o++ = '0';
    } else {
        *o++ = '0'; *o++ = '.';
        for (int i = 0; i < -e - 1; i++) *o++ = '0';
        memcpy(o, digits, (size_t)n); o += n;
    }
    *o = 0;
    puts(out);
}

/* ---- owned heap strings (docs/MEMORY.md section 3). A `&String` arrives as a pointer to the slot holding the
 * KdString*; an owned String is the KdString* itself (NULL after a move). */
typedef struct { char *data; int64_t len, cap; } KdString;
static int64_t kd_live = 0;

static void *xmalloc(int32_t line, int32_t col, size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) kd_fail(line, col, "out of memory", 13);
    return p;
}

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
        free(s->data);
        s->data = nd;
        s->cap = nc;
    }
    if (n) memcpy(s->data + s->len, p, (size_t)n);
    s->len += n;
}
int64_t kd_string_len(KdString **s) { return (*s)->len; }
int32_t kd_string_eq(KdString **a, KdString **b) { return (*a)->len == (*b)->len && ((*a)->len == 0 || memcmp((*a)->data, (*b)->data, (size_t)(*a)->len) == 0); }
void kd_print_string(KdString **s) { fwrite((*s)->data, 1, (size_t)(*s)->len, stdout); fputc('\n', stdout); }
void kd_string_drop(KdString *s) {
    if (!s) return;
    free(s->data);
    free(s);
    kd_live--;
}

/* ---- owned growable vectors of scalars (docs/MEMORY.md section 3b). A `&Vec` arrives as a pointer to the slot
 * holding the KdVec*. Element access returns a pointer into the buffer; the compiler emits the typed load/store. */
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
        free(v->data);
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
        die_prefix(line, col);
        fputs("vector index out of bounds: the index is ", stderr);
        put_int(idx, idx_unsigned);
        fprintf(stderr, " but the length is %lld\n", (long long)v->len);
        exit(2);
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
    free(v->data);
    free(v);
    kd_live--;
}

/* ---- owned heap cells, `Box<T>` (docs/MEMORY.md section 3d). The compiler stores/loads the contents itself and
 * runs the contents' drop glue before calling kd_box_free. */
void *kd_box_new(int32_t line, int32_t col, int64_t sz) { void *p = xmalloc(line, col, (size_t)sz); kd_live++; return p; }
void kd_box_free(void *p) { if (!p) return; free(p); kd_live--; }

static void *thread_main(void *arg) { *(int *)arg = kd_entry(); return NULL; }

int main(void) {
    static char buf[1 << 16];
    setvbuf(stdout, buf, _IOFBF, sizeof buf);
    int rc = 0;
    pthread_attr_t at;
    pthread_t th;
    pthread_attr_init(&at);
    pthread_attr_setstacksize(&at, (size_t)512 * 1024 * 1024);
    if (pthread_create(&th, &at, thread_main, &rc) != 0) { fputs("fatal: cannot create main thread\n", stderr); return 70; }
    pthread_join(th, NULL);
    fflush(stdout);
    if (rc == 0 && kd_live != 0) {
        /* Drop elaboration guarantees this never happens; if it does, it is a compiler bug. */
        fprintf(stderr, "internal error: memory leak: %lld owned allocation(s) were not freed\n", (long long)kd_live);
        return 70;
    }
    return rc;
}
