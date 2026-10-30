//! M1.5 (part 4): generic functions. Type arguments are inferred from call arguments; each instantiation is
//! checked and compiled separately (monomorphization); there are no trait bounds yet, so a generic body is
//! checked per instantiation (template style) and an unused generic function is never body-checked.
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

#[test]
fn identity_and_multiple_instantiations() {
    assert_eq!(ok("fn id<T>(x: T) -> T { x } fn main() { print(id(5)); print(id(2.5)); print(id(true)); print(id(\"s\")); }"), "5\n2.5\ntrue\ns\n");
    assert_eq!(ok("fn id<T>(x: T) -> T { x } fn main() { let a: u8 = id(200); let b: i64 = id(7); print(a); print(b); }"), "200\n7\n");
    assert_eq!(ok("fn pair_first<A, B>(a: A, b: B) -> A { a } fn main() { print(pair_first(1, true)); print(pair_first(false, 2.0)); }"), "1\nfalse\n");
    assert_eq!(ok("fn twice<T>(x: T) -> T { id2(id2(x)) } fn id2<U>(x: U) -> U { x } fn main() { print(twice(9)); }"), "9\n");
}

#[test]
fn bodies_use_the_concrete_type() {
    assert_eq!(ok("fn double<T>(x: T) -> T { x + x } fn main() { print(double(21)); print(double(1.25)); }"), "42\n2.5\n");
    assert_eq!(ok("fn max<T>(a: T, b: T) -> T { if a > b { a } else { b } } fn main() { print(max(3, 9)); print(max(2.5, 1.5)); let x: u8 = 250; print(max(x, 3)); }"), "9\n2.5\n250\n");
    // overflow is detected in the instantiated type
    let r = run_differential("fn double<T>(x: T) -> T { x + x } fn main() { let a: u8 = 200; print(double(a)); }", None);
    assert!(matches!(r, Err(kendrah::RunError::Runtime(e)) if e.message == "integer overflow in addition (u8)"));
}

#[test]
fn aggregates_references_and_recursion() {
    assert_eq!(ok("struct P { x: i64 } fn id<T>(x: T) -> T { x } fn main() { let p = id(P { x: 4 }); print(p.x); let a = id([1, 2, 3]); print(a[2]); }"), "4\n3\n");
    assert_eq!(ok("fn first<T>(a: [T; 3]) -> T { a[0] } fn main() { print(first([7, 8, 9])); print(first([true, false, false])); }"), "7\ntrue\n");
    assert_eq!(ok("fn get<T>(a: &[T; 2], i: i64) -> T { a[i] } fn main() { let a = [1.5, 2.5]; print(get(&a, 1)); let b = [4, 5]; print(get(&b, 0)); }"), "2.5\n4\n");
    assert_eq!(ok("fn set<T>(r: &mut T, v: T) { *r = v; } fn main() { let mut a = 1; set(&mut a, 8); print(a); let mut b = true; set(&mut b, false); print(b); }"), "8\nfalse\n");
    assert_eq!(ok("fn rep<T>(x: T, n: i64) -> i64 { if n == 0 { 0 } else { 1 + rep(x, n - 1) } } fn main() { print(rep(true, 5)); print(rep(1, 3)); }"), "5\n3\n");
    assert_eq!(ok("enum E { A, B } fn id<T>(x: T) -> T { x } fn main() { match id(E::B) { E::A => print(1), E::B => print(2) } }"), "2\n");
}

#[test]
fn owned_strings_through_generics() {
    assert_eq!(ok("fn id<T>(x: T) -> T { x } fn main() { let s = id(string_from(\"hi\")); print(&s); let t = id(id(s)); print(string_len(&t)); }"), "hi\n2\n");
    assert_eq!(ok("fn drop_it<T>(x: T) { } fn main() { drop_it(string_from(\"a\")); drop_it(3); print(1); }"), "1\n");
    rejects("fn id<T>(x: T) -> T { x } fn main() { let s = string_from(\"a\"); let t = id(s); print(string_len(&s)); }", "moved value `s`");
    rejects("fn wrap<T>(x: T) -> [T; 1] { [x] } fn main() { let a = wrap(string_from(\"a\")); }", "cannot be stored in arrays");
}

#[test]
fn inference_and_misuse_errors() {
    rejects("fn f<T>() -> i64 { 1 } fn main() {}", "does not appear in a parameter or return type");
    rejects("fn f<T, T>(x: T) {} fn main() {}", "duplicate type parameter");
    rejects("fn same<T>(a: T, b: T) -> T { a } fn main() { same(1, true); }", "conflicting types for type parameter `T`");
    rejects("fn id<T>(x: T) -> T { x } fn main() { id(1, 2); }", "takes 1 argument");
    rejects("fn id<T>(x: T) -> T { x } fn main() { let a = [1]; let r = &a; id(r); }", "cannot be a reference type");
    rejects("fn bad<T>(x: T) -> T { x + x } fn main() { bad(true); }", "in instantiation `bad<bool>`");
    rejects("fn poly<T>(x: T) -> i64 { poly([x]) } fn main() { poly(1); }", "too many generic instantiations");
    assert_eq!(ok("fn unused<T>(x: T) -> T { x + } fn main() { print(1); }".replace("x + }", "x }").as_str()), "1\n");
}

#[test]
fn layers_and_modules() {
    assert_eq!(ok("mod m { pub fn id<T>(x: T) -> T { x } } fn main() { print(m::id(3)); }"), "3\n");
    rejects("@layer(hardware) fn id<T>(x: T) -> T { x } @layer(declarative) fn g() -> i64 { id(1) } fn main() {}", "declarative");
}
