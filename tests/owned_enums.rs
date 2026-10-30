//! M4.6: enums whose payloads own heap memory (`String`, `Vec`, owning structs, other owning enums, generic
//! instances such as `Opt<String>`), consumed by value with `match`. HIR, UIR and native must agree, and the leak
//! checks of all three must stay quiet (a leak or double free is exit 70 natively / an internal error in the interpreters).
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

const M: &str = "enum Ms { Some(String), None } enum Pair { Two(String, String), One(String), Zero } fn s(x: str) -> String { string_from(x) } ";

#[test]
fn bind_the_payload_and_drop_the_rest() {
    let src = format!("{}fn len_of(m: Ms) -> i64 {{ match m {{ Ms::Some(t) => string_len(&t), Ms::None => 0 }} }}
        fn main() {{ print(len_of(Ms::Some(s(\"hello\")))); print(len_of(Ms::None)); }}", M);
    assert_eq!(ok(&src), "5\n0\n");
}

#[test]
fn unbound_payloads_are_dropped_by_the_match() {
    // `_` leaves `b` owned by the scrutinee: it must still be freed exactly once
    let src = format!("{}fn left(p: Pair) -> String {{ match p {{ Pair::Two(a, _) => a, Pair::One(a) => a, Pair::Zero => s(\"zero\") }} }}
        fn main() {{ let a = left(Pair::Two(s(\"l\"), s(\"r\"))); print(&a); let b = left(Pair::One(s(\"o\"))); print(&b); let c = left(Pair::Zero); print(&c); }}", M);
    assert_eq!(ok(&src), "l\no\nzero\n");
    let src = format!("{}fn f(p: Pair) -> i64 {{ match p {{ Pair::Two(_, _) => 2, Pair::One(_) => 1, _ => 0 }} }}
        fn main() {{ print(f(Pair::Two(s(\"a\"), s(\"b\")))); print(f(Pair::One(s(\"c\")))); print(f(Pair::Zero)); }}", M);
    assert_eq!(ok(&src), "2\n1\n0\n");
}

#[test]
fn bindings_are_owned_and_can_be_moved_on() {
    let src = format!("{}fn eat(x: String) -> i64 {{ string_len(&x) }}
        fn main() {{ let m = Ms::Some(s(\"abc\")); let n = match m {{ Ms::Some(t) => eat(t), Ms::None => 0 }}; print(n);
            let k = match Ms::Some(s(\"kept\")) {{ Ms::Some(t) => t, Ms::None => s(\"\") }}; print(&k); }}", M);
    assert_eq!(ok(&src), "3\nkept\n");
}

#[test]
fn matching_in_loops_reinitialises_bindings() {
    let src = format!("{}fn eat(x: String) {{ }}
        fn main() {{ let mut i = 0; let mut tot = 0; while i < 4 {{
            let m = if i == 2 {{ Ms::None }} else {{ Ms::Some(s(\"xy\")) }};
            match m {{ Ms::Some(t) => {{ tot = tot + string_len(&t); eat(t); }}, Ms::None => {{ tot = tot + 100; }} }}
            i = i + 1; }} print(tot); }}", M);
    assert_eq!(ok(&src), "106\n");
}

#[test]
fn return_and_break_inside_an_arm_drop_the_bindings() {
    let src = format!("{}fn f(m: Ms) -> i64 {{ match m {{ Ms::Some(t) => {{ if string_len(&t) > 2 {{ return 1; }} 2 }}, Ms::None => 3 }} }}
        fn main() {{ print(f(Ms::Some(s(\"long\")))); print(f(Ms::Some(s(\"a\")))); print(f(Ms::None));
            let mut i = 0; while true {{ match Ms::Some(s(\"b\")) {{ Ms::Some(t) => {{ i = i + 1; if i == 3 {{ break; }} }}, Ms::None => {{ }} }} }} print(i); }}", M);
    assert_eq!(ok(&src), "1\n2\n3\n3\n");
}

#[test]
fn nested_owning_enums_and_literal_subpatterns() {
    let src = "enum Inner { A(String), B } enum Outer { Wrap(Inner, i64), Plain(String) }
        fn go(o: Outer) -> i64 { match o { Outer::Wrap(Inner::A(t), 7) => string_len(&t) + 1000, Outer::Wrap(Inner::A(t), n) => string_len(&t) + n, Outer::Wrap(Inner::B, n) => n, Outer::Plain(t) => string_len(&t), _ => 0 } }
        fn main() { print(go(Outer::Wrap(Inner::A(string_from(\"ab\")), 7))); print(go(Outer::Wrap(Inner::A(string_from(\"ab\")), 8)));
            print(go(Outer::Wrap(Inner::B, 5))); print(go(Outer::Plain(string_from(\"xyz\")))); }";
    assert_eq!(ok(src), "1002\n10\n5\n3\n");
}

#[test]
fn binding_a_whole_inner_enum_moves_it() {
    let src = "enum Inner { A(String), B } enum Outer { Wrap(Inner), Nothing }
        fn unwrap(o: Outer) -> Inner { match o { Outer::Wrap(i) => i, Outer::Nothing => Inner::B } }
        fn main() { match unwrap(Outer::Wrap(Inner::A(string_from(\"deep\")))) { Inner::A(t) => print(&t), Inner::B => print(0) } }";
    assert_eq!(ok(src), "deep\n");
}

#[test]
fn enum_with_vec_and_struct_payloads() {
    let src = "struct P { name: String, n: i64 } enum E { V(Vec<i64>), S(P), Nil }
        fn sum(e: E) -> i64 { match e { E::V(v) => { let mut i = 0; let mut t = 0; while i < vec_len(&v) { t = t + v[i]; i = i + 1; } t }, E::S(p) => p.n + string_len(&p.name), E::Nil => 0 } }
        fn main() { let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 4); vec_push(&mut v, 5);
            print(sum(E::V(v))); print(sum(E::S(P { name: string_from(\"abc\"), n: 10 }))); print(sum(E::Nil)); }";
    assert_eq!(ok(src), "9\n13\n0\n");
}

#[test]
fn owned_enums_inside_structs_and_generic_instances() {
    let src = "struct Slot { v: Opt<String>, id: i64 } enum Opt<T> { Some(T), None }
        fn mk(i: i64) -> Slot { if i > 0 { Slot { v: Opt::Some(string_from(\"on\")), id: i } } else { Slot { v: Opt::None, id: i } } }
        fn show(s: Slot) -> i64 { let id = s.id; match s.v { Opt::Some(t) => string_len(&t) + id, Opt::None => id } }
        fn main() { print(show(mk(3))); print(show(mk(0))); }";
    // matching on a field of an owning struct moves a field out: rejected in this version
    rejects(src, "cannot move the owned field");
    let src = "struct Slot { v: Opt<String>, id: i64 } enum Opt<T> { Some(T), None }
        fn mk(i: i64) -> Slot { if i > 0 { Slot { v: Opt::Some(string_from(\"on\")), id: i } } else { Slot { v: Opt::None, id: i } } }
        fn main() { let a = mk(3); let b = mk(0); print(a.id + b.id); }";
    assert_eq!(ok(src), "3\n");
    let src = "enum Opt<T> { Some(T), None }
        fn first(o: Opt<String>) -> i64 { match o { Opt::Some(t) => string_len(&t), Opt::None => -1 } }
        fn wrap<T>(x: T) -> Opt<T> { Opt::Some(x) }
        fn main() { print(first(wrap(string_from(\"four\")))); let n: Opt<String> = Opt::None; print(first(n)); }";
    assert_eq!(ok(src), "4\n-1\n");
}

#[test]
fn assigning_over_an_owning_enum_drops_the_old_value() {
    let src = format!("{}fn main() {{ let mut m = Ms::Some(s(\"old\")); m = Ms::Some(s(\"new\")); m = Ms::None;
        match m {{ Ms::Some(t) => print(&t), Ms::None => print(0) }} }}", M);
    assert_eq!(ok(&src), "0\n");
}

#[test]
fn a_runtime_error_inside_an_arm_with_live_owned_values_is_reported_identically() {
    let src = format!("{}fn main() {{ let m = Ms::Some(s(\"x\")); match m {{ Ms::Some(t) => {{ let z = string_len(&t) - 1; print(10 / z); }}, Ms::None => {{ }} }} }}", M);
    let a = run_differential(&src, None).unwrap_err();
    let b = kendrah::native::run_native_differential(&src, 1).unwrap_err();
    assert!(format!("{:?}", a).contains("division by zero"), "{:?}", a);
    assert!(format!("{:?}", b).contains("division by zero"), "{:?}", b);
}

#[test]
fn use_after_match_is_a_move_error() {
    rejects(&format!("{}fn main() {{ let m = Ms::Some(s(\"a\")); match m {{ Ms::Some(t) => {{ }}, Ms::None => {{ }} }} match m {{ Ms::Some(t) => {{ }}, Ms::None => {{ }} }} }}", M), "use of moved value `m`");
    rejects(&format!("{}fn eat(x: String) {{ }} fn main() {{ let m = Ms::Some(s(\"a\")); match m {{ Ms::Some(t) => {{ eat(t); eat(t); }}, Ms::None => {{ }} }} }}", M), "use of moved value `t`");
    rejects(&format!("{}fn main() {{ let m = Ms::Some(s(\"a\")); let n = m; let k = m; }}", M), "use of moved value `m`");
}

#[test]
fn still_rejected_restrictions() {
    rejects("fn main() { let a = string_from(\"x\"); match a { t => { } } }", "cannot `match` on an owned `String`");
    rejects("enum E { A(String) } fn main() { let a = [E::A(string_from(\"x\"))]; }", "cannot be stored in arrays");
    rejects("enum E { A([String; 2]) } fn main() {}", "cannot be stored in arrays");
    rejects(&format!("{}fn f(r: &Ms) {{ match *r {{ Ms::Some(t) => {{ }}, Ms::None => {{ }} }} }} fn main() {{ }}", M), "out of a reference");
    rejects(&format!("{}fn f(m: Ms) -> i64 {{ match m {{ Ms::Some(t) => 1 }} }} fn main() {{ }}", M), "non-exhaustive");
}

#[test]
fn owned_enums_also_agree_on_wasm32() {
    let src = format!("{}fn left(p: Pair) -> String {{ match p {{ Pair::Two(a, _) => a, Pair::One(a) => a, Pair::Zero => s(\"zero\") }} }}
        fn main() {{ let mut i = 0; while i < 50 {{ let a = left(Pair::Two(s(\"l\"), s(\"r\"))); if i == 49 {{ print(&a); }} i = i + 1; }} let z = left(Pair::Zero); print(&z); }}", M);
    let a = run_differential(&src, None).unwrap();
    let w = kendrah::native::run_wasm_differential(&src, 1).unwrap_or_else(|e| panic!("wasm {:?}", e));
    assert_eq!(a, w);
    assert_eq!(a, "l\nzero\n");
}
