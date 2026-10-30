//! M4.4: owned `Vec<T>` of scalar elements (integers, f64, bool). Move-only, dropped exactly once, leak-checked;
//! all engines (HIR interp, UIR interp, native). Builtins: vec_new/push/len/get/set/pop/clone.
use kendrah::run_differential;

fn ok(src: &str) -> String {
    let a = run_differential(src, None).unwrap_or_else(|e| panic!("{:?}\n{}", e, src));
    let b = kendrah::native::run_native_differential(src, 1).unwrap_or_else(|e| panic!("native {:?}\n{}", e, src));
    assert_eq!(a, b);
    a
}
fn rejects(src: &str, needle: &str) {
    match kendrah::compile(src) {
        Err(ds) => { let m = ds.iter().map(|d| d.message.clone()).collect::<Vec<_>>().join("\n"); assert!(m.contains(needle), "{} not in {}", needle, m); }
        Ok(_) => panic!("expected error {}\n{}", needle, src),
    }
}
fn runtime_err(src: &str, msg: &str) {
    match run_differential(src, None) { Err(kendrah::RunError::Runtime(e)) => assert_eq!(e.message, msg), o => panic!("{:?}", o) }
}

#[test]
fn basic_operations() {
    assert_eq!(ok("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 10); vec_push(&mut v, 20); vec_push(&mut v, 30); print(vec_len(&v)); print(vec_get(&v, 1)); vec_set(&mut v, 1, 99); print(vec_get(&v, 1)); print(vec_pop(&mut v)); print(vec_len(&v)); }"), "3\n20\n99\n30\n2\n");
    assert_eq!(ok("fn main() { let mut v: Vec<u8> = vec_new(); vec_push(&mut v, 255); print(vec_get(&v, 0)); let mut f: Vec<f64> = vec_new(); vec_push(&mut f, 1.5); print(vec_get(&f, 0)); let mut b: Vec<bool> = vec_new(); vec_push(&mut b, true); vec_push(&mut b, false); print(vec_get(&b, 1)); print(vec_get(&b, 0)); }"), "255\n1.5\nfalse\ntrue\n");
}

#[test]
fn growth_and_loops() {
    let src = "fn main() { let mut v: Vec<i64> = vec_new(); for i in 0..1000 { vec_push(&mut v, i * 2); } let mut s = 0; for i in 0..vec_len(&v) { s = s + vec_get(&v, i); } print(s); print(vec_len(&v)); }";
    assert_eq!(ok(src), "999000\n1000\n");
}

#[test]
fn ownership_moves_clone_and_functions() {
    assert_eq!(ok("fn fill(n: i64) -> Vec<i64> { let mut v: Vec<i64> = vec_new(); for i in 0..n { vec_push(&mut v, i); } v } fn total(v: &Vec<i64>) -> i64 { let mut s = 0; for i in 0..vec_len(v) { s = s + vec_get(v, i); } s } fn main() { let v = fill(5); print(total(&v)); let w = v; print(total(&w)); }"), "10\n10\n");
    assert_eq!(ok("fn main() { let mut a: Vec<i64> = vec_new(); vec_push(&mut a, 1); let b = vec_clone(&a); vec_push(&mut a, 2); print(vec_len(&a)); print(vec_len(&b)); }"), "2\n1\n");
    assert_eq!(ok("fn push2(v: &mut Vec<i64>) { vec_push(v, 1); vec_push(v, 2); } fn main() { let mut v: Vec<i64> = vec_new(); push2(&mut v); print(vec_get(&v, 1)); }"), "2\n");
    // early return / break drop the vector
    assert_eq!(ok("fn f(n: i64) -> i64 { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, n); if n > 0 { return vec_get(&v, 0); } 0 } fn main() { print(f(3)); print(f(0)); let mut i = 0; while true { let mut w: Vec<i64> = vec_new(); vec_push(&mut w, i); i = i + 1; if i == 3 { break; } } print(i); }"), "3\n0\n3\n");
}

#[test]
fn generics_and_hints() {
    assert_eq!(ok("fn first<T>(v: &Vec<T>) -> T { vec_get(v, 0) } fn main() { let mut a: Vec<i64> = vec_new(); vec_push(&mut a, 7); let mut b: Vec<bool> = vec_new(); vec_push(&mut b, true); print(first(&a)); print(first(&b)); }"), "7\ntrue\n");
    assert_eq!(ok("fn mk() -> Vec<u8> { vec_new() } fn main() { let v = mk(); print(vec_len(&v)); }"), "0\n");
}

#[test]
fn runtime_errors() {
    runtime_err("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 1); print(vec_get(&v, 1)); }", "vector index out of bounds: the index is 1 but the length is 1");
    runtime_err("fn main() { let mut v: Vec<i64> = vec_new(); vec_set(&mut v, 0, 1); }", "vector index out of bounds: the index is 0 but the length is 0");
    runtime_err("fn main() { let mut v: Vec<i64> = vec_new(); let x = vec_pop(&mut v); print(x); }", "pop from an empty Vec");
    runtime_err("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 1); let i = -1; print(vec_get(&v, i)); }", "vector index out of bounds: the index is -1 but the length is 1");
}

#[test]
fn native_runtime_errors_match() {
    for (src, frag) in [
        ("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 1); print(vec_get(&v, 5)); }", "vector index out of bounds: the index is 5 but the length is 1"),
        ("fn main() { let mut v: Vec<u8> = vec_new(); let x = vec_pop(&mut v); print(x); }", "pop from an empty Vec"),
    ] {
        let r = kendrah::native::run_native_differential(src, 1);
        let m = format!("{:?}", r);
        assert!(m.contains(frag), "{}", m);
    }
}

#[test]
fn rejected_programs() {
    rejects("fn main() { let v = vec_new(); }", "cannot infer the element type");
    rejects("fn main() { let v: Vec<String> = vec_new(); }", "`Vec` elements must be integers");
    rejects("fn main() { let v: Vec = 1; }", "needs an element type");
    rejects("fn main() { let mut v: Vec<i64> = vec_new(); let w = v; vec_push(&mut v, 1); }", "moved");
    rejects("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, true); }", "mismatched types");
    rejects("fn main() { let v: Vec<i64> = vec_new(); vec_push(&v, 1); }", "mismatched types");
    rejects("fn main() { let mut v: Vec<i64> = vec_new(); vec_get(&v, 1.5); }", "index must be an integer");
    rejects("fn main() { let v: Vec<i64> = vec_new(); print(&v); }", "cannot print");
    rejects("fn main() { let v: Vec<i64> = vec_new(); match v { _ => {} } }", "cannot `match` on an owned");
    rejects("fn vec_len() {} fn main() {}", "is a builtin");
    rejects("@layer(declarative) fn f() -> i64 { let v: Vec<i64> = vec_new(); 1 } fn main() {}", "not permitted in @layer(declarative)");
}

#[test]
fn leaks_are_impossible_for_discarded_values() {
    // a fresh vector that is never bound is still freed
    assert_eq!(ok("fn mk() -> Vec<i64> { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 1); v } fn main() { mk(); print(1); }"), "1\n");
}

#[test]
fn index_sugar() {
    assert_eq!(ok("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 1); vec_push(&mut v, 2); v[0] = v[1] + 40; print(v[0]); let mut s = 0; for i in 0..vec_len(&v) { s = s + v[i]; } print(s); }"), "42\n44\n");
    assert_eq!(ok("fn bump(v: &mut Vec<u8>) { v[0] = v[0] + 1; } fn get(v: &Vec<u8>) -> u8 { v[0] } fn main() { let mut v: Vec<u8> = vec_new(); vec_push(&mut v, 4); bump(&mut v); print(get(&v)); }"), "5\n");
    runtime_err("fn main() { let mut v: Vec<i64> = vec_new(); v[0] = 1; }", "vector index out of bounds: the index is 0 but the length is 0");
    rejects("fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 1); v[0] = true; }", "mismatched types");
    rejects("fn main() { let v: Vec<i64> = vec_new(); v[0] = 1; }", "cannot borrow `v` as mutable");
    rejects("fn f(v: &Vec<i64>) { v[0] = 1; } fn main() {}", "shared reference");
}
