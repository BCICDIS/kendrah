//! M1.5 (part 5): generic structs and enums. Each distinct argument list is a separate monomorphized type
//! (named like `Pair<i64, bool>`); arguments are inferred from constructor operands or an expected type
//! (`let` annotation, parameter, return type, assignment target). No trait bounds, no explicit `::<>` syntax.
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

const OPT: &str = "enum Opt<T> { Some(T), None } ";

#[test]
fn generic_struct_inferred_and_annotated() {
    assert_eq!(ok("struct Pair<A, B> { a: A, b: B } fn main() { let p = Pair { a: 1, b: true }; print(p.a); print(p.b); let q: Pair<u8, f64> = Pair { a: 200, b: 1.5 }; print(q.a); print(q.b); }"), "1\ntrue\n200\n1.5\n");
    assert_eq!(ok("struct Pair<A, B> { a: A, b: B } fn sum(p: Pair<u8, u8>) -> u8 { p.a + p.b } fn main() { print(sum(Pair { a: 100, b: 100 })); }"), "200\n");
    // same arguments share one type; different arguments are different types
    rejects("struct P<T> { x: T } fn main() { let a: P<i64> = P { x: 1 }; let b: P<u8> = a; }", "mismatched types");
}

#[test]
fn generic_enum_construct_and_match() {
    let src = format!("{}fn get(o: Opt<i64>) -> i64 {{ match o {{ Opt::Some(v) => v, Opt::None => -1 }} }} fn main() {{ print(get(Opt::Some(7))); let n: Opt<i64> = Opt::None; print(get(n)); }}", OPT);
    assert_eq!(ok(&src), "7\n-1\n");
    let src = format!("{}fn main() {{ let a = Opt::Some(true); match a {{ Opt::Some(b) => print(b), Opt::None => print(false) }} let c = Opt::Some(2.5); match c {{ Opt::Some(x) => print(x), _ => {{}} }} }}", OPT);
    assert_eq!(ok(&src), "true\n2.5\n");
}

#[test]
fn hints_from_return_assignment_and_nesting() {
    let src = format!("{}fn find(a: [i64; 3], k: i64) -> Opt<i64> {{ for i in 0..3 {{ if a[i] == k {{ return Opt::Some(i); }} }} Opt::None }} fn main() {{ match find([5, 6, 7], 7) {{ Opt::Some(i) => print(i), Opt::None => print(-1) }} match find([5, 6, 7], 9) {{ Opt::Some(i) => print(i), Opt::None => print(-1) }} }}", OPT);
    assert_eq!(ok(&src), "2\n-1\n");
    let src = format!("{}fn main() {{ let mut o: Opt<u8> = Opt::Some(3); o = Opt::None; match o {{ Opt::None => print(1), _ => print(0) }} }}", OPT);
    assert_eq!(ok(&src), "1\n");
    // nested generics, including the `>>` token
    let src = format!("{}struct W<T> {{ v: T }} fn main() {{ let x: Opt<Opt<i64>> = Opt::Some(Opt::None); match x {{ Opt::Some(Opt::None) => print(1), _ => print(0) }} let w: W<Opt<u8>> = W {{ v: Opt::Some(9) }}; match w.v {{ Opt::Some(n) => print(n), Opt::None => print(0) }} }}", OPT);
    assert_eq!(ok(&src), "1\n9\n");
}

#[test]
fn generics_combine_with_generic_functions_and_modules() {
    let src = format!("{}fn wrap<T>(x: T) -> Opt<T> {{ Opt::Some(x) }} fn unwrap_or<T>(o: Opt<T>, d: T) -> T {{ match o {{ Opt::Some(v) => v, Opt::None => d }} }} fn main() {{ print(unwrap_or(wrap(5), 0)); print(unwrap_or(wrap(true), false)); let n: Opt<f64> = Opt::None; print(unwrap_or(n, 0.5)); }}", OPT);
    assert_eq!(ok(&src), "5\ntrue\n0.5\n");
    assert_eq!(ok("mod m { pub struct B<T> { v: T } pub fn mk(x: i64) -> B<i64> { B { v: x } } } fn main() { let b = m::mk(4); print(b.v); let c: m::B<bool> = m::B { v: true }; print(c.v); }"), "4\ntrue\n");
    assert_eq!(ok("struct Pair<A, B> { a: A, b: B } fn swap<A, B>(p: Pair<A, B>) -> Pair<B, A> { Pair { a: p.b, b: p.a } } fn main() { let s = swap(Pair { a: 1, b: true }); print(s.a); print(s.b); }"), "true\n1\n");
}

#[test]
fn value_semantics_and_arrays() {
    assert_eq!(ok("struct B<T> { v: [T; 2] } fn main() { let mut a = B { v: [1, 2] }; let b = a; a.v[0] = 9; print(a.v[0]); print(b.v[0]); }"), "9\n1\n");
    let src = format!("{}fn main() {{ let xs = [Opt::Some(1), Opt::None, Opt::Some(3)]; let mut t = 0; for i in 0..3 {{ match xs[i] {{ Opt::Some(v) => {{ t = t + v; }} Opt::None => {{}} }} }} print(t); }}", OPT);
    // array literal elements need a common instance: `Opt::None` alone cannot be inferred
    rejects(&src, "cannot infer type parameter `T`");
}

#[test]
fn rejected_programs() {
    rejects("struct P<T> { x: T } fn main() { let p: P = P { x: 1 }; }", "is generic");
    rejects("struct P<T> { x: T } fn main() { let p: P<i64, i64> = P { x: 1 }; }", "takes 1 type argument(s) but 2");
    rejects("struct P { x: i64 } fn main() { let p: P<i64> = P { x: 1 }; }", "is not generic");
    rejects(&format!("{}fn main() {{ let n = Opt::None; }}", OPT), "cannot infer type parameter `T`");
    rejects("struct P<T> { x: T, y: T } fn main() { let p = P { x: 1, y: true }; }", "conflicting types for type parameter `T`");
    rejects("struct L<T> { v: T, next: L<T> } fn main() { let a: L<i64> = L { v: 1, next: 2 }; }", "infinite size");
    rejects("struct P<T> { x: Missing } fn main() { }", "unknown type `Missing`");
    rejects(&format!("{}fn main() {{ let a: Opt<i64> = Opt::Some(1); match a {{ Opt::Some(v) => print(v) }} }}", OPT), "non-exhaustive");
    rejects(&format!("{}enum Q<T> {{ A(T) }} fn main() {{ let a: Opt<i64> = Opt::Some(1); match a {{ Q::A(v) => print(v), _ => {{}} }} }}", OPT), "is of generic type");
    rejects("struct W<T> { x: W<[T; 2]> } fn main() { let w: W<i64> = W { x: 1 }; }", "too many generic type instantiations");
}

#[test]
fn parser_rejections() {
    rejects("struct P<> { x: i64 } fn main() {}", "type parameter name");
    rejects("struct P<T, T> { x: T } fn main() {}", "duplicate type parameter");
    rejects("struct P<T> { x: T } fn main() { let p: P<i64 = P { x: 1 }; }", "`>`");
}
