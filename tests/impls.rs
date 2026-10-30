//! M1.5 (part 6): `impl` blocks: associated functions (`Type::f`), methods (`recv.m()` with `self`, `&self`,
//! `&mut self`), `Self`, generic impls (`impl<T> Opt<T>`), and method sugar for `Vec` / `String`.
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
fn associated_functions_and_methods() {
    assert_eq!(ok("struct P { x: i64, y: i64 } impl P { fn new(x: i64, y: i64) -> P { P { x: x, y: y } } fn sum(&self) -> i64 { self.x + self.y } fn scale(&mut self, k: i64) { self.x = self.x * k; self.y = self.y * k; } fn into_x(self) -> i64 { self.x } } fn main() { let mut p = P::new(2, 3); print(p.sum()); p.scale(10); print(p.sum()); print(p.into_x()); }"), "5\n50\n20\n");
    // Self in types, paths and literals
    assert_eq!(ok("struct C { n: i64 } impl C { fn zero() -> Self { Self { n: 0 } } fn inc(&mut self) -> Self { Self { n: self.n + 1 } } fn get(&self) -> i64 { self.n } } fn main() { let mut c = C::zero(); let d = c.inc(); print(d.get()); print(Self::x_is_not_here_but_unused()); }".replace(" print(Self::x_is_not_here_but_unused());", "").as_str()), "1\n");
}

#[test]
fn methods_on_enums_and_chained_calls() {
    assert_eq!(ok("enum Shape { Circle(i64), Square(i64) } impl Shape { fn area(&self) -> i64 { match *self { Shape::Circle(r) => r * r * 3, Shape::Square(s) => s * s } } fn double(self) -> Shape { match self { Shape::Circle(r) => Shape::Circle(r * 2), Shape::Square(s) => Shape::Square(s * 2) } } } fn main() { let s = Shape::Square(4); print(s.area()); print(s.double().double().area()); }"), "16\n256\n");
}

#[test]
fn methods_through_references_and_owned_structs() {
    assert_eq!(ok("struct Acc { total: i64 } impl Acc { fn add(&mut self, v: i64) { self.total = self.total + v; } fn get(&self) -> i64 { self.total } } fn feed(a: &mut Acc) { a.add(5); a.add(6); } fn read(a: &Acc) -> i64 { a.get() } fn main() { let mut a = Acc { total: 0 }; feed(&mut a); a.add(1); print(read(&a)); }"), "12\n");
    assert_eq!(ok("struct Person { name: String, scores: Vec<i64> } impl Person { fn new(n: str) -> Person { let s: Vec<i64> = vec_new(); Person { name: string_from(n), scores: s } } fn add_score(&mut self, v: i64) { self.scores.push(v); } fn count(&self) -> i64 { self.scores.len() } fn name_len(&self) -> i64 { self.name.len() } } fn main() { let mut p = Person::new(\"alice\"); p.add_score(3); p.add_score(4); print(p.count()); print(p.name_len()); }"), "2\n5\n");
}

#[test]
fn generic_impls() {
    let src = "enum Opt<T> { Some(T), None } impl<T> Opt<T> { fn is_some(&self) -> bool { match *self { Opt::Some(_) => true, Opt::None => false } } fn unwrap_or(self, d: T) -> T { match self { Opt::Some(v) => v, Opt::None => d } } fn none() -> Opt<T> { Opt::None } fn some(v: T) -> Opt<T> { Opt::Some(v) } } fn main() { let a = Opt::some(5); print(a.is_some()); print(a.unwrap_or(0)); let n: Opt<i64> = Opt::none(); print(n.is_some()); print(n.unwrap_or(9)); let b = Opt::some(true); print(b.unwrap_or(false)); }";
    assert_eq!(ok(src), "true\n5\nfalse\n9\ntrue\n");
    assert_eq!(ok("struct Pair<A, B> { a: A, b: B } impl<A, B> Pair<A, B> { fn first(&self) -> A { self.a } fn second(&self) -> B { self.b } fn new(a: A, b: B) -> Self { Pair { a: a, b: b } } } fn main() { let p = Pair::new(1, 2.5); print(p.first()); print(p.second()); }"), "1\n2.5\n");
}

#[test]
fn builtin_method_sugar() {
    assert_eq!(ok("fn main() { let mut v: Vec<i64> = vec_new(); v.push(4); v.push(5); print(v.len()); print(v.get(1)); v.set(0, 9); print(v[0]); print(v.pop()); let w = v.clone(); print(w.len()); let mut s = string_from(\"ab\"); s.push(\"cd\"); print(s.len()); print(&s); }"), "2\n5\n9\n5\n1\n4\nabcd\n");
    assert_eq!(ok("fn fill(v: &mut Vec<i64>) { v.push(1); v.push(2); } fn main() { let mut v: Vec<i64> = vec_new(); fill(&mut v); print(v.len()); }"), "2\n");
}

#[test]
fn modules_privacy_and_layers() {
    assert_eq!(ok("mod geo { pub struct P { x: i64 } impl P { pub fn new(x: i64) -> P { P { x: x } } pub fn x(&self) -> i64 { self.x } fn secret(&self) -> i64 { 1 } } } fn main() { let p = geo::P::new(7); print(p.x()); }"), "7\n");
    rejects("mod geo { pub struct P { x: i64 } impl P { fn secret(&self) -> i64 { 1 } pub fn new() -> P { P { x: 0 } } } } fn main() { let p = geo::P::new(); print(p.secret()); }", "is private to module");
    assert_eq!(ok("struct P { x: i64 } @layer(hardware) impl P { fn hw(&self) -> i64 { self.x } } fn main() { let p = P { x: 3 }; print(p.hw()); }"), "3\n");
}

#[test]
fn rejected_programs() {
    rejects("struct P { x: i64 } fn main() { let p = P { x: 1 }; p.nope(); }", "has no method `nope`");
    rejects("struct P { x: i64 } impl P { fn new() -> P { P { x: 0 } } } fn main() { let p = P::new(); p.new(); }", "associated function, not a method");
    rejects("struct P { x: i64 } impl P { fn f(&self) {} fn f(&self) {} } fn main() {}", "defined more than once");
    rejects("impl Missing { fn f() {} } fn main() {}", "unknown type `Missing`");
    rejects("fn f() {} impl f { fn g() {} } fn main() {}", "cannot have an `impl`");
    rejects("enum E { A } impl E { fn A() {} } fn main() {}", "conflicts with a variant");
    rejects("struct P<T> { x: T } impl P { fn f() {} } fn main() {}", "has 1 type parameter(s) but the `impl` names 0");
    rejects("struct P<T> { x: T } impl<T> P<i64> { fn f() {} } fn main() {}", "must be the impl's own type parameters");
    rejects("fn main() { let x = 1; x.foo(); }", "has no methods");
    rejects("struct P { x: i64 } impl P { fn inc(&mut self) { self.x = self.x + 1; } } fn main() { let p = P { x: 1 }; p.inc(); }", "cannot borrow `p` as mutable");
    rejects("struct P { x: i64 } impl P { fn inc(&mut self) { self.x = self.x + 1; } } fn f(p: &P) { p.inc(); } fn main() {}", "shared reference");
    rejects("struct S { n: String } impl S { fn take(self) {} } fn f(s: &S) { s.take(); } fn main() {}", "cannot move an owned value out of a reference");
    rejects("fn main() { let x = Self { }; }", "`Self` is only available inside an `impl` block");
    rejects("struct P { x: i64 } impl P { let y = 1; } fn main() {}", "only `fn` items");
    rejects("struct P { x: i64 } impl P { fn f(&self) {} } fn main() { P::f(); }", "takes 1 argument(s) but 0");
}

#[test]
fn temporary_receivers_are_bound_and_dropped() {
    assert_eq!(ok("struct Person { name: String } impl Person { fn new(n: str) -> Person { Person { name: string_from(n) } } fn name_len(&self) -> i64 { self.name.len() } } fn main() { print(Person::new(\"alice\").name_len()); }"), "5\n");
    assert_eq!(ok("fn mk() -> Vec<i64> { let mut v: Vec<i64> = vec_new(); v.push(1); v.push(2); v } fn main() { print(mk().len()); }"), "2\n");
}
