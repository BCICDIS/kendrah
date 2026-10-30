//! M4.5: structs that own `String` / `Vec` fields (and structs of such structs, and generic instances such as
//! `Pair<String, Vec<i64>>`). Move-only; recursive drop glue; no moving a field out of its struct; HIR, UIR, native.
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

const PERSON: &str = "struct Person { name: String, age: i64, scores: Vec<i64> } fn mk(n: str, a: i64) -> Person { let mut s: Vec<i64> = vec_new(); vec_push(&mut s, a); Person { name: string_from(n), age: a, scores: s } } ";

#[test]
fn construct_read_and_drop() {
    assert_eq!(ok(&format!("{}fn main() {{ let p = mk(\"ann\", 30); print(&p.name); print(p.age); print(vec_len(&p.scores)); print(p.scores[0]); print(string_len(&p.name)); }}", PERSON)), "ann\n30\n1\n30\n3\n");
}

#[test]
fn moves_of_whole_structs() {
    assert_eq!(ok(&format!("{}fn take(p: Person) -> i64 {{ p.age }} fn main() {{ let p = mk(\"bob\", 7); let q = p; print(take(q)); }}", PERSON)), "7\n");
    assert_eq!(ok(&format!("{}fn pass(p: Person) -> Person {{ p }} fn main() {{ let p = pass(pass(mk(\"id\", 1))); print(&p.name); }}", PERSON)), "id\n");
    // conditional move: dropped on the path that did not move it
    assert_eq!(ok(&format!("{}fn eat(p: Person) {{ }} fn main() {{ let mut i = 0; while i < 3 {{ let p = mk(\"x\", i); if i == 1 {{ eat(p); }} i = i + 1; }} print(i); }}", PERSON)), "3\n");
    // early return and break
    assert_eq!(ok(&format!("{}fn f(n: i64) -> i64 {{ let p = mk(\"r\", n); if n > 0 {{ return p.age; }} 0 }} fn main() {{ print(f(5)); print(f(0)); let mut i = 0; while true {{ let q = mk(\"b\", i); i = i + 1; if i == 2 {{ break; }} }} print(i); }}", PERSON)), "5\n0\n2\n");
}

#[test]
fn field_borrows_and_mutation() {
    assert_eq!(ok(&format!("{}fn grow(p: &mut Person) {{ string_push(&mut p.name, \"!\"); vec_push(&mut p.scores, 9); p.age = p.age + 1; }} fn show(p: &Person) {{ print(&p.name); print(p.age); print(vec_len(&p.scores)); }} fn main() {{ let mut p = mk(\"cy\", 1); grow(&mut p); grow(&mut p); show(&p); }}", PERSON)), "cy!!\n3\n3\n");
    // overwriting an owned field drops the old value
    assert_eq!(ok(&format!("{}fn main() {{ let mut p = mk(\"old\", 1); p.name = string_from(\"new\"); p.scores = vec_clone(&p.scores); print(&p.name); }}", PERSON)), "new\n");
    // overwriting a whole struct
    assert_eq!(ok(&format!("{}fn main() {{ let mut p = mk(\"a\", 1); p = mk(\"b\", 2); print(&p.name); }}", PERSON)), "b\n");
    assert_eq!(ok(&format!("{}fn main() {{ let p = mk(\"zz\", 1); let n = string_clone(&p.name); print(&n); print(string_eq(&n, &p.name)); }}", PERSON)), "zz\ntrue\n");
}

#[test]
fn nested_and_generic_owners() {
    assert_eq!(ok("struct In { s: String } struct Out { a: In, b: In, n: i64 } fn main() { let o = Out { a: In { s: string_from(\"x\") }, b: In { s: string_from(\"y\") }, n: 3 }; print(&o.a.s); print(&o.b.s); print(o.n); }"), "x\ny\n3\n");
    assert_eq!(ok("struct Pair<A, B> { a: A, b: B } fn main() { let p = Pair { a: string_from(\"k\"), b: 5 }; print(&p.a); print(p.b); let mut v: Vec<i64> = vec_new(); vec_push(&mut v, 8); let q = Pair { a: v, b: string_from(\"w\") }; print(q.a[0]); print(&q.b); }"), "k\n5\n8\nw\n");
    // moving fields out of a struct (partial moves) is not supported yet
    rejects("struct Pair<A, B> { a: A, b: B } fn swap<A, B>(p: Pair<A, B>) -> Pair<B, A> { Pair { a: p.b, b: p.a } } fn main() { let s = swap(Pair { a: string_from(\"k\"), b: 5 }); }", "cannot move the owned field");
}

#[test]
fn discarded_temporaries_are_dropped() {
    assert_eq!(ok(&format!("{}fn main() {{ mk(\"tmp\", 1); print(1); }}", PERSON)), "1\n");
}

#[test]
fn rejected_programs() {
    rejects(&format!("{}fn main() {{ let p = mk(\"a\", 1); let n = p.name; }}", PERSON), "cannot move the owned field `name`");
    rejects(&format!("{}fn main() {{ let p = mk(\"a\", 1); let q = p; print(p.age); }}", PERSON), "moved");
    rejects(&format!("{}fn main() {{ let p = mk(\"a\", 1); let q = p; let r = p; }}", PERSON), "use of moved value");
    rejects(&format!("{}fn main() {{ let n = mk(\"a\", 1).age; }}", PERSON), "temporary owned value");
    rejects(&format!("{}fn main() {{ let mut p = mk(\"a\", 1); let q = p; p.age = 2; }}", PERSON), "assignment to a field of moved value");
    rejects(&format!("{}fn f(p: &Person) -> Person {{ *p }} fn main() {{ }}", PERSON), "cannot move an owned");
    rejects(&format!("{}fn main() {{ let a = [mk(\"a\", 1)]; }}", PERSON), "cannot be stored in arrays");
    rejects(&format!("{}struct H {{ a: [Person; 2] }} fn main() {{ }}", PERSON), "cannot be stored in arrays");
    rejects(&format!("{}fn main() {{ let p = mk(\"a\", 1); let r = &p.name; let q = p; print(r); }}", PERSON), "borrow");
}
