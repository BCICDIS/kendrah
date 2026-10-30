//! M1.5 (part 2): `use` imports (private, per-module aliases; no re-export, no globs).
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
        Ok(_) => panic!("expected error {}", needle),
    }
}

#[test]
fn imports_functions_types_and_variants() {
    assert_eq!(ok("mod m { pub fn f() -> i64 { 7 } } use crate::m::f; fn main() { print(f()); }"), "7\n");
    assert_eq!(ok("mod m { pub fn f() -> i64 { 7 } } use crate::m::f as g; fn main() { print(g()); }"), "7\n");
    assert_eq!(ok("mod geo { pub struct P { pub x: i64 } pub fn mk() -> P { P { x: 3 } } } use crate::geo::P; use crate::geo::mk; fn main() { let p: P = mk(); print(p.x); }".replace("pub x", "x").as_str()), "3\n");
    assert_eq!(ok("mod e { pub enum C { R, G } } use crate::e::C; fn main() { let c = C::G; match c { C::R => print(1), C::G => print(2) } }"), "2\n");
    assert_eq!(ok("mod a { pub mod b { pub fn f() -> i64 { 1 } } } use crate::a::b; fn main() { print(b::f()); }"), "1\n");
}

#[test]
fn imports_are_per_module_and_private() {
    assert_eq!(ok("mod m { pub fn f() -> i64 { 5 } } mod n { use crate::m::f; pub fn g() -> i64 { f() + 1 } } fn main() { print(n::g()); }"), "6\n");
    rejects("mod m { pub fn f() -> i64 { 5 } } mod n { use crate::m::f; pub fn g() -> i64 { 1 } } fn main() { print(n::f()); }", "");
    rejects("mod m { pub fn f() -> i64 { 5 } } use crate::m::f; mod n { pub fn g() -> i64 { f() } } fn main() { print(n::g()); }", "");
}

#[test]
fn bad_imports_are_rejected() {
    rejects("use crate::nope::f; fn main() {}", "unresolved import");
    rejects("mod m { fn f() {} } use crate::m::f; fn main() {}", "private");
    rejects("pub use crate::m::f; fn main() {}", "re-export");
    rejects("mod m { pub fn f() {} } use crate::m::f; fn f() {} fn main() {}", "more than once");
    rejects("mod m { pub fn f() {} } use crate::m::f; use crate::m::f; fn main() {}", "more than once");
    rejects("use a::x; use a as q; fn main() {}", "");
}

#[test]
fn local_items_shadow_nothing_and_aliases_do_not_leak() {
    rejects("mod m { pub fn f() -> i64 { 1 } } use crate::m::f as g; fn main() { print(f()); }", "");
}
