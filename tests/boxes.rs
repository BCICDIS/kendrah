//! M4.7: `Box<T>` (owned heap cell; recursive types through Box). Consuming access (`box_into`), copying access for
//! non-owned contents (`box_get`/`box_set`). HIR, UIR, native and wasm must agree; all leak checks must stay quiet.
use kendrah::run_differential;

/// The interpreters recurse natively per Kendrah call (and the tests recurse 2000 deep), so run on a big stack like the CLI does.
fn big<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|sc| std::thread::Builder::new().stack_size(256 * 1024 * 1024).spawn_scoped(sc, f).unwrap().join().unwrap())
}

fn ok(src: &str) -> String {
    big(|| {
        let a = run_differential(src, None).unwrap_or_else(|e| panic!("{:?}\n{}", e, src));
        let b = kendrah::native::run_native_differential(src, 1).unwrap_or_else(|e| panic!("native {:?}\n{}", e, src));
        assert_eq!(a, b);
        a
    })
}
fn rejects(src: &str, needle: &str) {
    match kendrah::compile(src) {
        Err(ds) => { let m = ds.iter().map(|d| d.message.clone()).collect::<Vec<_>>().join("\n"); assert!(m.contains(needle), "{} not in {}", needle, m); }
        Ok(_) => panic!("expected error {}\n{}", needle, src),
    }
}

const LIST: &str = "enum List { Cons(i64, Box<List>), Nil }
fn build(n: i64) -> List { let mut l = List::Nil; let mut i = 0; while i < n { l = List::Cons(i, box_new(l)); i = i + 1; } l }
fn sum(l: List) -> i64 { match l { List::Cons(h, t) => h + sum(box_into(t)), List::Nil => 0 } }
";

#[test]
fn linked_list_build_consume_and_drop() {
    assert_eq!(ok(&format!("{}fn main() {{ print(sum(build(10))); let unused = build(5); print(1); }}", LIST)), "45\n1\n");
}

#[test]
fn very_long_chains_are_dropped_without_recursion_trouble() {
    // 300k nodes: freed by drop glue (native recursion, wasm host stack, iterative interpreter free)
    assert_eq!(ok(&format!("{}fn main() {{ let big = build(300000); print(7); }}", LIST)), "7\n");
}

#[test]
fn binary_tree_with_two_boxes() {
    let src = "enum Tree { Node(Box<Tree>, i64, Box<Tree>), Leaf }
        fn insert(t: Tree, v: i64) -> Tree { match t { Tree::Leaf => Tree::Node(box_new(Tree::Leaf), v, box_new(Tree::Leaf)),
            Tree::Node(l, x, r) => if v < x { Tree::Node(box_new(insert(box_into(l), v)), x, r) } else { Tree::Node(l, x, box_new(insert(box_into(r), v))) } } }
        fn sum(t: Tree) -> i64 { match t { Tree::Leaf => 0, Tree::Node(l, x, r) => sum(box_into(l)) + x + sum(box_into(r)) } }
        fn depth(t: Tree) -> i64 { match t { Tree::Leaf => 0, Tree::Node(l, _, r) => { let a = depth(box_into(l)); let b = depth(box_into(r)); if a > b { a + 1 } else { b + 1 } } } }
        fn main() { let mut t = Tree::Leaf; let mut i = 0; while i < 20 { t = insert(t, (i * 7) % 20); i = i + 1; } print(sum(t)); let u = insert(insert(Tree::Leaf, 2), 1); print(depth(u)); }";
    assert_eq!(ok(src), "190\n2\n");
}

#[test]
fn box_get_and_set_copy_scalar_and_aggregate_contents() {
    let src = "struct P { x: i64, y: f64 } fn main() { let b = box_new(41); let mut c = box_new(1); box_set(&mut c, box_get(&b) + 1); print(box_get(&c));
        let mut p = box_new(P { x: 3, y: 0.5 }); let q = box_get(&p); print(q.x); box_set(&mut p, P { x: 9, y: 1.5 }); print(box_get(&p).y); print(box_get(&b)); }";
    assert_eq!(ok(src), "42\n3\n1.5\n41\n");
}

#[test]
fn boxes_can_hold_owned_values_and_nest() {
    let src = "struct W { s: String, n: i64 } fn main() { let b: Box<String> = box_new(string_from(\"boxed\")); let s = box_into(b); print(&s);
        let w = box_new(W { s: string_from(\"abc\"), n: 4 }); let inner = box_into(w); print(string_len(&inner.s) + inner.n);
        let bb = box_new(box_new(5)); let b2 = box_into(bb); print(box_get(&b2));
        let dropped = box_new(string_from(\"never read\")); }";
    assert_eq!(ok(src), "boxed\n7\n5\n");
}

#[test]
fn boxes_in_struct_fields_and_generics() {
    let src = "struct Cell<T> { v: Box<T>, tag: i64 } enum Opt<T> { Some(T), None }
        fn mk<T>(x: T, tag: i64) -> Cell<T> { Cell { v: box_new(x), tag: tag } }
        fn main() { let c = mk(10, 1); print(box_get(&c.v) + c.tag); let d = mk(string_from(\"gen\"), 2); print(d.tag);
            let o: Opt<Box<i64>> = Opt::Some(box_new(8)); match o { Opt::Some(b) => print(box_get(&b)), Opt::None => print(0) } }";
    assert_eq!(ok(src), "11\n2\n8\n");
}

#[test]
fn assigning_over_a_box_drops_the_old_cell() {
    let src = "fn main() { let mut b = box_new(string_from(\"one\")); b = box_new(string_from(\"two\")); let s = box_into(b); print(&s); }";
    assert_eq!(ok(src), "two\n");
}

#[test]
fn deep_recursion_through_boxes_hits_the_call_depth_limit_identically() {
    let src = format!("{}fn main() {{ print(sum(build(3000))); }}", LIST);
    let (a, b) = big(|| (run_differential(&src, None).unwrap_err(), kendrah::native::run_native_differential(&src, 1).unwrap_err()));
    assert!(format!("{:?}", a).contains("call depth exceeded 2000"), "{:?}", a);
    assert!(format!("{:?}", b).contains("call depth exceeded 2000"), "{:?}", b);
}

#[test]
fn boxes_agree_on_wasm32() {
    let src = format!("{}fn main() {{ print(sum(build(50))); let big = build(100000); let s = box_into(box_new(string_from(\"x\"))); print(&s); }}", LIST);
    let (a, w) = big(|| (run_differential(&src, None).unwrap(), kendrah::native::run_wasm_differential(&src, 1).unwrap_or_else(|e| panic!("wasm {:?}", e))));
    assert_eq!(a, w);
    assert_eq!(a, "1225\nx\n");
}

#[test]
fn rejected_programs() {
    rejects("fn main() { let b = box_new(string_from(\"x\")); let c = box_get(&b); }", "is owned");
    rejects("fn main() { let b = box_new(1); box_set(&b, 2); }", "mutable reference");
    rejects("fn main() { let b = box_new(1); let n = box_into(b); let m = box_into(b); }", "use of moved value `b`");
    rejects("fn main() { let x = 1; let r = &x; let b = box_new(r); }", "cannot be used as a value");
    rejects("fn f(b: Box<&i64>) {} fn main() {}", "cannot be returned, nested or stored");
    rejects("fn main() { let a = [box_new(1)]; }", "cannot be stored in arrays");
    rejects("fn main() { let n = box_into(5); }", "expects a `Box<T>`");
    rejects("fn main() { let b: Box<i64, i64> = box_new(1); }", "takes 1 type argument");
    rejects("struct S { a: S } fn main() {}", "infinite size");
    rejects("enum L { C(i64, L), N } fn main() {}", "infinite size");
    rejects("@layer(declarative) fn f() -> i64 { let b = box_new(1); 0 } fn main() {}", "heap allocation");
}
