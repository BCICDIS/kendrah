//! M4.2: second-class references and the borrow checker (docs/MEMORY.md section 2).
//! Positive programs run on HIR interpreter, UIR interpreter and native code and must agree.
use kendrah::{run_differential, RunError};

fn ok(src: &str) -> String {
    let a = match run_differential(src, None) { Ok(o) => o, Err(e) => panic!("{:?}\n{}", e, src) };
    let b = match kendrah::native::run_native_differential(src, 1) { Ok(o) => o, Err(e) => panic!("native: {:?}\n{}", e, src) };
    assert_eq!(a, b, "HIR/UIR vs native output differ for\n{}", src);
    a
}

fn rt_err(src: &str) -> String {
    let a = match run_differential(src, None) { Err(RunError::Runtime(e)) => e.message, o => panic!("expected runtime error, got {:?}\n{}", o, src) };
    let b = match kendrah::native::run_native_differential(src, 1) { Err(RunError::Runtime(e)) => e.message, o => panic!("native: expected runtime error, got {:?}", o) };
    assert_eq!(a, b);
    a
}

/// Compile errors: all messages joined (the program must be rejected before running).
fn cerr(src: &str) -> String {
    match kendrah::compile(src) {
        Err(ds) => ds.iter().map(|d| format!("{}:{}: {}", d.span.line, d.span.col, d.message)).collect::<Vec<_>>().join("\n"),
        Ok(_) => panic!("expected a compile error for\n{}", src),
    }
}

fn rejects(src: &str, needle: &str) {
    let m = cerr(src);
    assert!(m.contains(needle), "expected `{}` in:\n{}\nfor program\n{}", needle, m, src);
}

fn accepts(src: &str) { if let Err(e) = kendrah::compile(src) { panic!("{:?}\n{}", e, src) } }

// ------------------------------------------------------------------ behaviour

#[test]
fn mutation_through_references() {
    assert_eq!(ok("fn inc(x: &mut i64) { *x = *x + 1; } fn main() { let mut a = 5; inc(&mut a); inc(&mut a); print(a); }"), "7\n");
    assert_eq!(ok("fn main() { let mut a = 1; { let r = &mut a; *r = *r + 41; } print(a); }"), "42\n");
    assert_eq!(ok("fn get(x: &i64) -> i64 { *x } fn main() { let a = 9; let r = &a; print(get(r)); print(*r); print(get(&a)); }"), "9\n9\n9\n");
    assert_eq!(ok("fn main() { let mut f = 1.5; let mut b = false; let mut s = \"x\"; { let r = &mut f; *r = *r * 2.0; let q = &mut b; *q = true; let w = &mut s; *w = \"y\"; } print(f); print(b); print(s); }"), "3.0\ntrue\ny\n");
}

#[test]
fn arrays_through_references_are_not_copied() {
    let src = "fn fill(a: &mut [i64; 5], v: i64) { let mut i = 0; while i < len(a) { a[i] = v + i; i = i + 1; } }
fn sum(a: &[i64; 5]) -> i64 { let mut s = 0; let mut i = 0; while i < len(a) { s = s + a[i]; i = i + 1; } s }
fn main() { let mut x = [0; 5]; fill(&mut x, 10); print(sum(&x)); print(x[4]); let y = x; fill(&mut x, 0); print(y[0]); print(x[0]); }";
    assert_eq!(ok(src), "60\n14\n10\n0\n");
    // 1,000 calls over a 200,000-element array: would be 2e8 element copies if the array were passed by value.
    let big = "fn bump(a: &mut [i64; 200000], i: i64) { a[i] = a[i] + 1; } fn main() { let mut a = [0; 200000]; let mut k = 0; while k < 1000 { bump(&mut a, k * 7); k = k + 1; } print(a[0]); print(a[7]); print(a[6993]); }";
    assert_eq!(ok(big), "1\n1\n1\n");
}

#[test]
fn struct_fields_elements_and_disjoint_borrows() {
    let p = "struct P { x: i64, y: i64 } struct W { p: P, a: [i64; 3] }";
    assert_eq!(ok(&format!("{p} fn swap(a: &mut i64, b: &mut i64) {{ let t = *a; *a = *b; *b = t; }} fn main() {{ let mut q = P {{ x: 1, y: 2 }}; swap(&mut q.x, &mut q.y); print(q.x); print(q.y); }}")), "2\n1\n");
    assert_eq!(ok(&format!("{p} fn setx(p: &mut P, v: i64) {{ p.x = v; }} fn sumxy(p: &P) -> i64 {{ p.x + p.y }} fn main() {{ let mut q = P {{ x: 1, y: 2 }}; setx(&mut q, 40); print(sumxy(&q)); }}")), "42\n");
    assert_eq!(ok(&format!("{p} fn main() {{ let mut w = W {{ p: P {{ x: 1, y: 2 }}, a: [5, 6, 7] }}; {{ let r = &mut w.a[1]; *r = 60; let s = &mut w.p.y; *s = 20; }} print(w.a[1]); print(w.p.y); print(w.a[0]); }}")), "60\n20\n5\n");
    assert_eq!(ok(&format!("{p} fn f(w: &mut W) {{ w.p.x = w.p.x + 1; w.a[2] = w.a[0] + w.a[1]; }} fn main() {{ let mut w = W {{ p: P {{ x: 1, y: 2 }}, a: [5, 6, 7] }}; f(&mut w); f(&mut w); print(w.p.x); print(w.a[2]); }}")), "3\n11\n");
    assert_eq!(ok("fn main() { let mut g = [[0; 3]; 2]; { let row = &mut g[1]; row[2] = 8; } let r = &g; print(r[1][2]); print(r[0][0]); }"), "8\n0\n");
}

#[test]
fn reborrowing_and_recursion() {
    assert_eq!(ok("fn inc(x: &mut i64) { *x = *x + 1; } fn twice(x: &mut i64) { inc(x); inc(x); } fn main() { let mut a = 0; twice(&mut a); twice(&mut a); print(a); }"), "4\n");
    assert_eq!(ok("fn main() { let mut a = 1; let r = &mut a; { let r2 = &mut *r; *r2 = 5; } *r = *r + 1; print(*r); }"), "6\n");
    assert_eq!(ok("fn fill(a: &mut [i64; 6], i: i64) { if i == 6 { return; } a[i] = i * i; fill(a, i + 1); } fn main() { let mut a = [0; 6]; fill(&mut a, 0); print(a[5]); print(a[3]); }"), "25\n9\n");
    assert_eq!(ok("fn rd(x: &i64) -> i64 { *x } fn f(r: &mut i64) -> i64 { *r = 3; rd(r) } fn main() { let mut a = 0; print(f(&mut a)); print(a); }"), "3\n3\n");
    assert_eq!(ok("fn two(a: &i64, b: &i64) -> i64 { *a + *b } fn main() { let a = 20; print(two(&a, &a)); let r = &a; let s = &a; print(two(r, s)); }"), "40\n40\n");
}

#[test]
fn sorting_in_place_matches_a_reference_result() {
    let src = "fn sort(a: &mut [i64; 8]) { let mut i = 0; while i < len(a) { let mut j = 0; while j + 1 < len(a) - i { if a[j] > a[j + 1] { let t = a[j]; a[j] = a[j + 1]; a[j + 1] = t; } j = j + 1; } i = i + 1; } }
fn main() { let mut a = [5, 3, 9, 1, 7, 2, 8, 0]; sort(&mut a); let mut i = 0; while i < 8 { print(a[i]); i = i + 1; } }";
    assert_eq!(ok(src), "0\n1\n2\n3\n5\n7\n8\n9\n");
}

#[test]
fn enums_and_match_on_dereferenced_values() {
    let e = "enum S { A, B(i64) }";
    assert_eq!(ok(&format!("{e} fn f(s: &S) -> i64 {{ match *s {{ S::A => 0, S::B(v) => v }} }} fn set(s: &mut S) {{ *s = S::B(9); }} fn main() {{ let mut s = S::A; print(f(&s)); set(&mut s); print(f(&s)); }}")), "0\n9\n");
}

#[test]
fn runtime_errors_through_references() {
    assert_eq!(rt_err("fn f(a: &mut [i64; 3], i: i64) { a[i] = 1; } fn main() { let mut a = [0; 3]; f(&mut a, 3); }"), "array index out of bounds: the index is 3 but the length is 3");
    // an out-of-bounds borrow is caught when the borrow is created
    assert_eq!(rt_err("fn main() { let mut a = [0; 3]; let i = 5; let r = &mut a[i]; *r = 1; }"), "array index out of bounds: the index is 5 but the length is 3");
    assert_eq!(rt_err("fn f(x: &mut i32) { *x = *x + 1; } fn main() { let mut a: i32 = 2147483647; f(&mut a); }"), "integer overflow in addition (i32)");
}

#[test]
fn references_work_in_declarative_code_when_shared() {
    assert_eq!(ok("@layer(declarative) fn get(a: &[i64; 3], i: i64) -> i64 { a[i] * 2 } fn main() { let a = [1, 2, 3]; print(get(&a, 2)); }"), "6\n");
}

// ------------------------------------------------------------------ static rejection

#[test]
fn conflicting_loans_are_rejected() {
    rejects("fn main() { let mut a = 1; let r = &mut a; a = 2; print(*r); }", "cannot assign to `a` because it is borrowed");
    rejects("fn main() { let mut a = 1; let r = &mut a; print(a); *r = 2; }", "cannot use `a` because it is mutably borrowed");
    rejects("fn main() { let mut a = 1; let r = &a; a = 2; print(*r); }", "cannot assign to `a` because it is borrowed");
    rejects("fn main() { let mut a = 1; let r = &mut a; let s = &mut a; *r = 1; *s = 2; }", "cannot borrow `a` as mutable because it is already borrowed");
    rejects("fn main() { let mut a = 1; let r = &a; let s = &mut a; print(*r); *s = 1; }", "cannot borrow `a` as mutable because it is already borrowed");
    rejects("fn main() { let mut a = 1; let r = &mut a; let s = &a; *r = 1; print(*s); }", "cannot borrow `a` as shared because it is mutably borrowed");
    rejects("fn main() { let mut a = 1; let r = &mut a; let q = &mut *r; let w = &mut *r; *q = 1; *w = 2; }", "already borrowed");
    rejects("fn main() { let mut a = 1; let r = &mut a; let q = &mut *r; *r = 5; *q = 2; }", "cannot assign to `*r` because it is borrowed");
}

#[test]
fn aliasing_within_one_call_is_rejected() {
    let f = "fn f(a: &mut i64, b: &i64) {} fn g(a: &mut i64, b: &mut i64) {} fn h(a: &mut i64, b: i64) {}";
    rejects(&format!("{f} fn main() {{ let mut a = 1; f(&mut a, &a); }}"), "cannot borrow `a` as shared because it is mutably borrowed");
    rejects(&format!("{f} fn main() {{ let mut a = 1; f(&mut a, &mut a); }}"), "cannot");
    rejects(&format!("{f} fn main() {{ let mut a = 1; g(&mut a, &mut a); }}"), "cannot borrow `a` as mutable because it is already borrowed");
    rejects(&format!("{f} fn main() {{ let mut a = 1; h(&mut a, a); }}"), "cannot use `a` because it is mutably borrowed");
    rejects(&format!("{f} fn main() {{ let mut a = 1; let r = &mut a; g(r, r); }}"), "already borrowed");
    rejects("fn g(a: &mut i64, b: &mut i64) {} struct P { x: i64, y: i64 } fn main() { let mut p = P { x: 1, y: 2 }; g(&mut p.x, &mut p.x); }", "already borrowed");
    // indices are not distinguished: documented conservative behaviour
    rejects("fn g(a: &mut i64, b: &mut i64) {} fn main() { let mut a = [1, 2]; g(&mut a[0], &mut a[1]); }", "already borrowed");
}

#[test]
fn safe_patterns_are_accepted() {
    accepts("fn g(a: &mut i64, b: &mut i64) {} struct P { x: i64, y: i64 } fn main() { let mut p = P { x: 1, y: 2 }; g(&mut p.x, &mut p.y); }");
    accepts("fn f(a: &i64, b: &i64) {} fn main() { let a = 1; f(&a, &a); let r = &a; let s = &a; print(*r + *s + a); }");
    accepts("fn main() { let mut a = 1; { let r = &mut a; *r = 2; } a = 3; let s = &a; print(*s); }");
    accepts("fn f(r: &mut i64) { { let q = &mut *r; *q = 1; } *r = 2; }");
    // documented imprecision (lexical loans, not NLL): `q` is dead after its last use but its loan lasts to the end of the block
    rejects("fn f(r: &mut i64) { let q = &mut *r; *q = 1; *r = 2; }", "cannot assign to `*r` because it is borrowed");
    accepts("fn main() { let mut a = 1; let b = a; let r = &mut a; *r = b; }");
}

#[test]
fn reference_rules_are_enforced_by_the_checker() {
    rejects("fn main() { let a = 1; let r = &mut a; *r = 2; }", "cannot borrow `a` as mutable (declare it with `let mut`)");
    rejects("fn f(r: &i64) { *r = 1; }", "cannot assign through the shared reference `r`");
    rejects("fn f(r: &i64) { let q = &mut *r; }", "because `r` is a shared reference");
    rejects("fn f(r: &i64) -> &i64 { r }", "references are only allowed as function parameter types");
    rejects("struct S { r: &i64 } fn main() {}", "references are only allowed as function parameter types");
    rejects("fn f(r: &&i64) {}", "references to references");
    rejects("fn main() { let mut a = 1; let r = &mut a; let q = r; }", "must be initialised with `&place`");
    rejects("fn main() { let mut a = 1; let r = &mut a; print(r); }", "a reference cannot be used as a value");
    rejects("fn main() { let mut a = 1; let r = &mut a; let b = r + 1; }", "a reference cannot be used as a value");
    rejects("fn main() { let mut a = 1; let mut b = 2; let r = &mut a; r = &mut b; }", "cannot assign to the reference binding `r`");
    rejects("fn main() { let mut a = 1; let mut r = &mut a; }", "cannot be `mut`");
    rejects("fn main() { let r = &5; }", "only a variable, field, element");
    rejects("fn f() -> i64 { 1 } fn main() { let r = &f(); }", "only a variable, field, element");
    rejects("fn f(r: &mut i64) {} fn main() { let a = 1; f(&a); }", "mismatched types in argument 1");
    rejects("fn f(r: &mut i64) {} fn main() { let mut a = 1; let r = &a; f(r); }", "mismatched types in argument 1");
    rejects("fn f(r: &i64) {} fn main() { let mut a = 1.5; f(&a); }", "mismatched types in argument 1");
    rejects("fn main() { let x = 1; let y = *x; }", "cannot dereference a value of type i64");
    rejects("fn main() { let mut a = 1; let r = &mut a; let r2 = &r; }", "cannot borrow the reference `r`");
    rejects("fn main() { let a = if true { &1 } else { &2 }; }", "only a variable, field, element");
    rejects("@layer(declarative) fn f() -> i64 { let mut a = 1; let r = &mut a; 1 }", "not permitted in @layer(declarative)");
    // `&mut T` coerces to `&T`, not the other way round
    accepts("fn r(a: &i64) {} fn w(a: &mut i64) { r(a); } fn main() { let mut x = 1; w(&mut x); }");
}
