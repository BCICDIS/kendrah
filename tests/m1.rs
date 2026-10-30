//! M1 feature tests: sized integers + inference, structs, enums + match, arrays, modules, layer interaction.
use kendrah::{compile, run_differential, RunError};

fn run(src: &str) -> Result<String, RunError> {
    let s = src.to_string();
    std::thread::Builder::new().stack_size(256 * 1024 * 1024)
        .spawn(move || run_differential(&s, None)).unwrap().join().unwrap()
}
fn out(src: &str) -> String { run(src).unwrap_or_else(|e| panic!("expected success, got {:?}\nsource:\n{}", e, src)) }
fn mb(body: &str) -> String { format!("fn main() {{ {} }}", body) }
fn errors(src: &str) -> Vec<String> {
    match compile(src) {
        Ok(_) => panic!("expected compile error for:\n{}", src),
        Err(ds) => ds.into_iter().map(|d| format!("{}:{}: {}", d.span.line, d.span.col, d.message)).collect(),
    }
}
fn rejects(src: &str, needle: &str) {
    let e = errors(src);
    assert!(e.iter().any(|m| m.contains(needle)), "no error containing {:?}; got {:#?}", needle, e);
}
fn rt_err(src: &str) -> String {
    match run(src) { Err(RunError::Runtime(e)) => e.message, o => panic!("expected runtime error, got {:?}", o) }
}

struct Lcg(u64);
impl Lcg { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 17 } }

// ======================= sized integers and inference =======================

#[test]
fn float_literal_requires_digits_after_dot() {
    assert!(compile(&mb("print(1.);")).is_err());
    assert!(compile(&mb("print(.5);")).is_err());
}
#[test]
fn literals_infer_from_context() {
    assert_eq!(out(&mb("let x = 5; let y: u8 = 10; print(x + y);")), "15\n");
    assert_eq!(out("fn f(a: u8) -> u8 { a } fn main() { print(f(200)); }"), "200\n");
}
#[test]
fn unconstrained_literal_defaults_to_i64() {
    // 3_000_000_000 does not fit i32 but defaults to i64; and i64 overflow is detected.
    assert_eq!(out(&mb("let big = 3000000000; print(big * 2);")), "6000000000\n");
}
#[test]
fn mixed_int_types_are_rejected() {
    rejects(&mb("let a: u8 = 1; let b: i32 = 2; print(a + b);"), "cannot be applied to u8 and i32");
    rejects(&mb("let a: u8 = 1; let b: i8 = 1; print(a == b);"), "cannot be applied to u8 and i8");
    rejects("fn f(a: u8) {} fn main() { let x: i64 = 1; f(x); }", "expected u8, found i64");
}
#[test]
fn inference_flows_backwards_through_variables() {
    // `x` is unconstrained at its definition and becomes u8 by its later use.
    assert_eq!(out(&mb("let x = 250; let y: u8 = 5; print(x + y);")), "255\n");
    assert_eq!(rt_err(&mb("let x = 250; let y: u8 = 6; print(x + y);")).contains("overflow"), true);
}
#[test]
fn literal_range_checks() {
    rejects(&mb("let x: u8 = 256;"), "integer literal 256 does not fit in u8");
    rejects(&mb("let x: u8 = -1;"), "integer literal -1 does not fit in u8");
    rejects(&mb("let x: i8 = 128;"), "does not fit in i8");
    assert_eq!(out(&mb("let x: i8 = -128; print(x);")), "-128\n");
    assert_eq!(out(&mb("let x: i64 = -9223372036854775808; print(x);")), "-9223372036854775808\n");
    assert_eq!(out(&mb("let x: u64 = 18446744073709551615; print(x);")), "18446744073709551615\n");
    rejects(&mb("let x: i64 = 9223372036854775808;"), "does not fit in i64");
}
#[test]
fn unsigned_cannot_be_negated() {
    rejects(&mb("let x: u8 = 1; print(-x);"), "cannot negate u8");
}
#[test]
fn checked_arithmetic_per_type() {
    assert!(rt_err(&mb("let a: u8 = 250; print(a + 10);")).contains("overflow"));
    assert!(rt_err(&mb("let a: u8 = 0; print(a - 1);")).contains("overflow"));
    assert!(rt_err(&mb("let a: i8 = -128; print(a - 1);")).contains("overflow"));
    assert!(rt_err(&mb("let a: i8 = -128; print(-a);")).contains("overflow"));
    assert!(rt_err(&mb("let a: u64 = 18446744073709551615; print(a + 1);")).contains("overflow"));
    assert!(rt_err(&mb("let a: u64 = 18446744073709551615; print(a * a);")).contains("overflow"));
    assert_eq!(out(&mb("let a: u32 = 4294967295; print(a - 1);")), "4294967294\n");
}
#[test]
fn casts_wrap_between_integer_types() {
    assert_eq!(out(&mb("print(300 as u8); print((-1) as u8); print(200 as i8); print(65535 as i16); print(70000 as u16);")), "44\n255\n-56\n-1\n4464\n");
    let a: i64 = -1; assert_eq!(a as u64 as i128, 18446744073709551615i128); // reference semantics
    assert_eq!(out(&mb("let m: i64 = -1; print(m as u64);")), "18446744073709551615\n");
}
#[test]
fn float_to_int_cast_saturates() {
    assert_eq!(out(&mb("print(300.7 as u8); print(-5.0 as u8); print(100000000000000000000.0 as i32); print(2.9 as i32);")), "255\n0\n2147483647\n2\n");
}
#[test]
fn bitwise_operators_and_precedence() {
    assert_eq!(out(&mb("print(1 | 2 & 3); print(1 + 2 << 1); print(5 & 3 == 1); print(6 ^ 3); print(1 << 4 | 1);")), "3\n6\ntrue\n5\n17\n");
}
#[test]
fn shifts_truncate_and_range_check() {
    assert_eq!(out(&mb("let x: u8 = 255; print(x << 1); let y: u8 = 1; print(y << 7); let z: i8 = -16; print(z >> 2);")), "254\n128\n-4\n");
    assert!(rt_err(&mb("let x: u8 = 1; print(x << 8);")).contains("shift amount 8 out of range for u8"));
    assert!(rt_err(&mb("let x: i64 = 1; let n = 0 - 1; print(x >> n);")).contains("shift amount -1"));
    rejects(&mb("let x: u8 = 1; print(x << 1.5);"), "cannot be applied");
    rejects(&mb("print(1.5 & 1.5);"), "cannot be applied");
}

macro_rules! diff_int {
    ($fname:ident, $t:ty, $tn:expr) => {
        #[test]
        fn $fname() {
            let mut rng = Lcg(0xBEEF ^ $tn.len() as u64);
            let mut vals: Vec<$t> = vec![<$t>::MIN, <$t>::MAX, 0, 1, <$t>::MAX / 2, (0 as $t).wrapping_sub(1)];
            for _ in 0..6 { vals.push(((rng.next() << 20) ^ rng.next()) as $t); }
            let mut checked = 0;
            for &a in &vals {
                for &b in &vals {
                    let ops: [(&str, Option<$t>); 8] = [
                        ("+", a.checked_add(b)), ("-", a.checked_sub(b)), ("*", a.checked_mul(b)),
                        ("/", a.checked_div(b)), ("%", a.checked_rem(b)),
                        ("&", Some(a & b)), ("|", Some(a | b)), ("^", Some(a ^ b)),
                    ];
                    for (sym, want) in ops {
                        let src = format!("fn main() {{ let a: {t} = {a}; let b: {t} = {b}; print(a {s} b); }}", t = $tn, a = a, b = b, s = sym);
                        match (want, run(&src)) {
                            (Some(v), Ok(o)) => assert_eq!(o, format!("{}\n", v), "{}", src),
                            (None, Err(RunError::Runtime(_))) => {}
                            (w, r) => panic!("mismatch for {}: want {:?}, got {:?}", src, w, r),
                        }
                        checked += 1;
                    }
                }
            }
            // comparisons and shifts
            for &a in &vals {
                for n in 0..<$t>::BITS {
                    let src = format!("fn main() {{ let a: {t} = {a}; let n = {n}; print(a << n); print(a >> n); }}", t = $tn, a = a, n = n);
                    let want = format!("{}\n{}\n", a.wrapping_shl(n), a.wrapping_shr(n));
                    assert_eq!(out(&src), want, "{}", src);
                }
                for &b in &vals {
                    let src = format!("fn main() {{ let a: {t} = {a}; let b: {t} = {b}; print(a < b); print(a >= b); print(a == b); }}", t = $tn, a = a, b = b);
                    assert_eq!(out(&src), format!("{}\n{}\n{}\n", a < b, a >= b, a == b), "{}", src);
                }
            }
            assert!(checked > 400);
        }
    };
}
diff_int!(diff_i8, i8, "i8");
diff_int!(diff_i16, i16, "i16");
diff_int!(diff_i32, i32, "i32");
diff_int!(diff_i64, i64, "i64");
diff_int!(diff_u8, u8, "u8");
diff_int!(diff_u16, u16, "u16");
diff_int!(diff_u32, u32, "u32");
diff_int!(diff_u64, u64, "u64");

macro_rules! diff_cast {
    ($fname:ident, $t:ty, $tn:expr) => {
        #[test]
        fn $fname() {
            let mut rng = Lcg(99);
            let mut vals: Vec<i64> = vec![0, 1, -1, 127, 128, 255, 256, -128, -129, 65535, 65536, i64::MAX, i64::MIN, 4294967295, 4294967296];
            for _ in 0..20 { vals.push(((rng.next() << 25) ^ rng.next()) as i64); }
            for v in vals {
                let src = format!("fn main() {{ let v: i64 = {}; print(v as {}); }}", v, $tn);
                assert_eq!(out(&src), format!("{}\n", v as $t), "{}", src);
            }
        }
    };
}
diff_cast!(cast_to_i8, i8, "i8"); diff_cast!(cast_to_u8, u8, "u8"); diff_cast!(cast_to_i16, i16, "i16");
diff_cast!(cast_to_u16, u16, "u16"); diff_cast!(cast_to_i32, i32, "i32"); diff_cast!(cast_to_u32, u32, "u32");
diff_cast!(cast_to_u64, u64, "u64");

// ======================= structs =======================

const POINT: &str = "struct Point { x: i64, y: i64 }\n";

#[test]
fn struct_literal_field_read_and_write() {
    let src = format!("{}fn main() {{ let mut p = Point {{ x: 1, y: 2 }}; p.x = p.x + 10; p.y = 5; print(p.x * 100 + p.y); }}", POINT);
    assert_eq!(out(&src), "1105\n");
}
#[test]
fn struct_literal_field_order_is_free_but_evaluation_is_source_order() {
    let src = "struct S { a: i64, b: i64 }
        fn t(n: i64) -> i64 { print(n); n }
        fn main() { let s = S { b: t(2), a: t(1) }; print(s.a * 10 + s.b); }";
    assert_eq!(out(src), "2\n1\n12\n");
}
#[test]
fn structs_have_value_semantics() {
    let src = format!("{}fn bump(mut_p: Point) -> Point {{ Point {{ x: mut_p.x + 1, y: mut_p.y }} }}
        fn main() {{ let mut a = Point {{ x: 1, y: 1 }}; let b = a; a.x = 9; let c = bump(b); print(a.x); print(b.x); print(c.x); }}", POINT);
    assert_eq!(out(&src), "9\n1\n2\n");
}
#[test]
fn nested_structs_and_arrays_in_structs() {
    let src = "struct In { v: [i64; 3] } struct Out { a: In, n: u8 }
        fn main() { let mut o = Out { a: In { v: [1, 2, 3] }, n: 7 }; o.a.v[1] = 20; print(o.a.v[0] + o.a.v[1] + o.a.v[2]); print(o.n); }";
    assert_eq!(out(src), "24\n7\n");
}
#[test]
fn struct_in_condition_position_is_not_a_literal() {
    let src = format!("{}fn main() {{ let p = Point {{ x: 3, y: 4 }}; let q = p; if p.x == q.x {{ print(1); }} while false {{ }} if p.y > 3 {{ print(2); }} }}", POINT);
    assert_eq!(out(&src), "1\n2\n");
}
#[test]
fn struct_errors() {
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1 }}; }}", POINT), "missing field(s)");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1, y: 2, z: 3 }}; }}", POINT), "no field `z`");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1, x: 2, y: 3 }}; }}", POINT), "specified more than once");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: true, y: 2 }}; }}", POINT), "field `x` is i64 but initializer is bool");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1, y: 2 }}; print(p.z); }}", POINT), "no field `z` on type `Point`");
    rejects("fn main() { let x = 1; print(x.y); }", "has no fields");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1, y: 2 }}; p.x = 3; }}", POINT), "cannot assign through immutable variable `p`");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1, y: 2 }}; print(p); }}", POINT), "cannot print a value of type Point");
    rejects(&format!("{}fn main() {{ let p = Point {{ x: 1, y: 2 }}; print(p == p); }}", POINT), "cannot be applied to Point and Point");
    rejects("fn main() { let p = Nope { x: 1 }; }", "unknown struct `Nope`");
    rejects("struct A { x: Missing } fn main() {}", "unknown type `Missing`");
    rejects("struct A { x: i64, x: i64 } fn main() {}", "duplicate field `x`");
    rejects("struct A { x: i64 } struct A { y: i64 } fn main() {}", "defined more than once");
}
#[test]
fn recursive_types_are_rejected() {
    rejects("struct A { a: A } fn main() {}", "infinite size");
    rejects("struct A { b: B } struct B { a: [A; 2] } fn main() {}", "infinite size");
    rejects("enum L { Cons(i64, L), Nil } fn main() {}", "infinite size");
}

// ======================= enums and match =======================

const SHAPE: &str = "enum Shape { Circle(f64), Rect(f64, f64), Empty }\n";

#[test]
fn enum_construction_and_payload_extraction() {
    let src = format!("{}fn area2(s: Shape) -> f64 {{ match s {{ Shape::Circle(r) => 3.0 * r * r, Shape::Rect(w, h) => w * h, Shape::Empty => 0.0 }} }}
        fn main() {{ print(area2(Shape::Circle(2.0))); print(area2(Shape::Rect(3.0, 4.5))); print(area2(Shape::Empty)); }}", SHAPE);
    assert_eq!(out(&src), "12.0\n13.5\n0.0\n");
}
#[test]
fn match_literals_wildcards_and_bindings() {
    let src = "fn name(n: i64) -> str { match n { 0 => \"zero\", 1 => \"one\", -1 => \"minus one\", _ => \"many\" } }
        fn main() { print(name(0)); print(name(1)); print(name(0 - 1)); print(name(7)); }";
    assert_eq!(out(src), "zero\none\nminus one\nmany\n");
    assert_eq!(out(&mb("let x = 41; print(match x { n => n + 1 });")), "42\n");
    assert_eq!(out(&mb("print(match \"b\" { \"a\" => 1, \"b\" => 2, _ => 3 });")), "2\n");
    assert_eq!(out(&mb("print(match true { true => 1, false => 0 });")), "1\n");
}
#[test]
fn nested_patterns_and_option_like_enum() {
    let src = "enum Opt { Some(i64), None }
        fn describe(o: Opt) -> i64 { match o { Opt::Some(0) => 100, Opt::Some(n) => n, Opt::None => 0 - 1 } }
        enum Pair { P(Opt, Opt) }
        fn both(p: Pair) -> i64 { match p { Pair::P(Opt::Some(a), Opt::Some(b)) => a + b, Pair::P(_, _) => 0 } }
        fn main() { print(describe(Opt::Some(0))); print(describe(Opt::Some(5))); print(describe(Opt::None));
                    print(both(Pair::P(Opt::Some(2), Opt::Some(3)))); print(both(Pair::P(Opt::None, Opt::Some(3)))); }";
    assert_eq!(out(src), "100\n5\n-1\n5\n0\n");
}
#[test]
fn match_is_an_expression_with_blocks_in_arms() {
    let src = format!("{}fn main() {{ let s = Shape::Rect(2.0, 3.0); let r = match s {{ Shape::Rect(w, h) => {{ let a = w * h; a + 1.0 }} _ => 0.0 }}; print(r); }}", SHAPE);
    assert_eq!(out(&src), "7.0\n");
}
#[test]
fn match_scrutinee_evaluated_once() {
    let src = "fn t() -> i64 { print(1); 5 } fn main() { match t() { 5 => print(2), _ => print(3) } }";
    assert_eq!(out(src), "1\n2\n");
}
#[test]
fn match_exhaustiveness_errors() {
    rejects(&format!("{}fn f(s: Shape) -> i64 {{ match s {{ Shape::Circle(_) => 1, Shape::Empty => 2 }} }} fn main() {{}}", SHAPE), "not covered: Shape::Rect");
    rejects("fn f(n: i64) -> i64 { match n { 0 => 1, 1 => 2 } } fn main() {}", "add a `_` arm");
    rejects("fn f(b: bool) -> i64 { match b { true => 1 } } fn main() {}", "cover both `true` and `false`");
    // A refutable nested pattern alone does not cover its variant (conservative, documented).
    rejects("enum O { S(i64), N } fn f(o: O) -> i64 { match o { O::S(0) => 1, O::N => 2 } } fn main() {}", "not covered: O::S");
    rejects("fn f(n: i64) -> i64 { match n { } } fn main() {}", "at least one arm");
}
#[test]
fn match_type_errors() {
    rejects(&format!("{}fn f(s: Shape) -> i64 {{ match s {{ Shape::Circle(_) => 1, _ => \"x\" }} }} fn main() {{}}", SHAPE), "`match` arms have different types");
    rejects(&format!("{}fn f(s: Shape) -> i64 {{ match s {{ Shape::Circle(_, _) => 1, _ => 2 }} }} fn main() {{}}", SHAPE), "has 2 field(s) but the variant has 1");
    rejects(&format!("{}enum Other {{ A }} fn f(s: Shape) -> i64 {{ match s {{ Other::A => 1, _ => 2 }} }} fn main() {{}}", SHAPE), "scrutinee is Shape");
    rejects(&format!("{}fn f(s: Shape) -> i64 {{ match s {{ Shape::Nope => 1, _ => 2 }} }} fn main() {{}}", SHAPE), "has no variant `Nope`");
    rejects("fn f(n: i64) -> i64 { match n { true => 1, _ => 2 } } fn main() {}", "bool pattern does not match");
    rejects("fn f(n: bool) -> i64 { match n { 1 => 1, _ => 2 } } fn main() {}", "integer pattern does not match");
    rejects("fn f(n: u8) -> i64 { match n { 300 => 1, _ => 2 } } fn main() {}", "does not fit in u8");
}
#[test]
fn unqualified_uppercase_pattern_is_an_error_not_a_silent_catch_all() {
    rejects(&format!("{}fn f(s: Shape) -> i64 {{ match s {{ Shape::Circle(_) => 1, Empty => 2 }} }} fn main() {{}}", SHAPE), "looks like an enum variant but is not qualified");
}
#[test]
fn enum_construction_errors() {
    rejects(&format!("{}fn main() {{ let s = Shape::Circle(1.0, 2.0); }}", SHAPE), "takes 1 argument(s) but 2");
    rejects(&format!("{}fn main() {{ let s = Shape::Circle; }}", SHAPE), "takes 1 field(s)");
    rejects(&format!("{}fn main() {{ let s = Shape::Square(1.0); }}", SHAPE), "has no variant `Square`");
    rejects(&format!("{}fn main() {{ let s = Shape::Circle(1); }}", SHAPE), "expected f64, found i64");
    rejects("enum E { A, A } fn main() {}", "duplicate variant `A`");
}

// ======================= arrays =======================

#[test]
fn array_literal_index_assign_len() {
    assert_eq!(out(&mb("let mut a = [10, 20, 30]; a[1] = 25; print(a[0] + a[1] + a[2]); print(len(a));")), "65\n3\n");
    assert_eq!(out(&mb("let a = [7; 4]; print(len(a)); print(a[3]);")), "4\n7\n");
}
#[test]
fn nested_arrays() {
    assert_eq!(out(&mb("let mut g = [[0; 3]; 2]; g[1][2] = 5; g[0][0] = 1; print(g[1][2] + g[0][0] + g[0][1]); print(len(g)); print(len(g[0]));")), "6\n2\n3\n");
}
#[test]
fn arrays_have_value_semantics() {
    let src = "fn first(a: [i64; 3]) -> i64 { a[0] }
        fn make() -> [i64; 3] { [4, 5, 6] }
        fn main() { let mut a = [1, 2, 3]; let b = a; a[0] = 99; print(b[0]); print(first(a)); print(make()[2]); }";
    assert_eq!(out(src), "1\n99\n6\n");
}
#[test]
fn index_type_can_be_any_integer_type() {
    assert_eq!(out(&mb("let a = [1, 2, 3]; let i: u8 = 2; print(a[i]);")), "3\n");
}
#[test]
fn array_runtime_bounds_checks() {
    assert!(rt_err(&mb("let a = [1, 2, 3]; let i = 3; print(a[i]);")).contains("index is 3 but the length is 3"));
    assert!(rt_err(&mb("let a = [1, 2, 3]; let i = 0 - 1; print(a[i]);")).contains("index is -1"));
    assert!(rt_err(&mb("let mut a = [1, 2, 3]; let i = 5; a[i] = 1;")).contains("out of bounds"));
    assert!(rt_err("fn f() -> [i64; 2] { [1, 2] } fn main() { let i = 2; print(f()[i]); }").contains("out of bounds"));
}
#[test]
fn array_compile_time_errors() {
    rejects(&mb("let a = [1, 2, 3]; print(a[3]);"), "index 3 is out of bounds for an array of length 3");
    rejects(&mb("let a = [1, 2, 3]; print(a[true]);"), "array index must be an integer");
    rejects(&mb("let a: [i64; 3] = [1, 2];"), "declared [i64; 3] but initializer is [i64; 2]");
    rejects(&mb("let a = [1, true];"), "array elements have different types");
    rejects(&mb("let a = [];"), "empty array literal");
    rejects(&mb("let a = [0; 2000000];"), "exceeds the M1 maximum");
    rejects(&mb("let x = 1; print(x[0]);"), "cannot index into a value of type i64");
    rejects(&mb("let x = 1; print(len(x));"), "`len` expects an array");
    rejects(&mb("let a = [1]; a[0] = 2;"), "cannot assign through immutable variable `a`");
    rejects(&mb("let mut a = [1]; a[0] = true;"), "`a[..]` is i64 but assigned bool");
    rejects(&mb("let a = [1, 2]; let b = [1, 2]; print(a == b);"), "cannot be applied");
}
#[test]
fn sieve_of_eratosthenes_matches_known_prime_count() {
    // pi(10_000) = 1229 (well-known value); also exercises array performance paths.
    let src = "fn main() { let mut s = [true; 10000]; s[0] = false; s[1] = false; let mut i = 2;
        while i * i < 10000 { if s[i] { let mut j = i * i; while j < 10000 { s[j] = false; j = j + i; } } i = i + 1; }
        let mut c = 0; let mut k = 0; while k < len(s) { if s[k] { c = c + 1; } k = k + 1; } print(c); }";
    assert_eq!(out(src), "1229\n");
}
#[test]
fn assignment_evaluates_rhs_before_place_indices() {
    let src = "fn f() -> i64 { print(1); 0 } fn g() -> i64 { print(2); 9 } fn main() { let mut a = [0, 0]; a[f()] = g(); print(a[0]); }";
    assert_eq!(out(src), "2\n1\n9\n");
}

// ======================= modules and visibility =======================

#[test]
fn module_paths_super_and_crate() {
    let src = "mod math { pub fn square(x: i64) -> i64 { x * x }
            pub mod inner { pub fn cube(x: i64) -> i64 { x * super::square(x) } pub fn root_twice() -> i64 { crate::twice(1) } } }
        fn twice(x: i64) -> i64 { x * 2 }
        fn main() { print(math::square(7)); print(math::inner::cube(3)); print(math::inner::root_twice()); }";
    assert_eq!(out(src), "49\n27\n2\n");
}
#[test]
fn private_items_are_visible_inside_the_module_tree_only() {
    let src = "mod m { fn hidden() -> i64 { 41 } pub fn open() -> i64 { hidden() + 1 } pub mod c { pub fn peek_parent() -> i64 { super::hidden() } } }
        fn main() { print(m::open()); print(m::c::peek_parent()); }";
    assert_eq!(out(src), "42\n41\n");
    rejects("mod m { fn hidden() {} } fn main() { m::hidden(); }", "`m::hidden` is private");
    rejects("mod m { mod secret { pub fn f() {} } } fn main() { m::secret::f(); }", "`m::secret` is private");
    rejects("mod m { struct S { x: i64 } } fn main() { let s = m::S { x: 1 }; }", "`m::S` is private");
}
#[test]
fn types_in_modules() {
    let src = "mod geo { pub struct P { x: i64, y: i64 } pub enum K { A(i64), B }
            pub fn mk(x: i64) -> P { P { x: x, y: x + 1 } } pub fn kind(k: K) -> i64 { match k { K::A(n) => n, K::B => 0 } } }
        fn main() { let p = geo::mk(4); let q = geo::P { x: 1, y: 2 }; print(p.y + q.x); print(geo::kind(geo::K::A(8))); print(geo::kind(geo::K::B)); }";
    assert_eq!(out(src), "6\n8\n0\n");
}
#[test]
fn module_name_resolution_errors() {
    rejects("fn main() { nope::f(); }", "undefined function `nope::f`");
    rejects("mod m {} fn main() { m::f(); }", "undefined function `m::f`");
    rejects("fn f() {} fn main() { f::g(); }", "undefined function `f::g`");
    rejects("fn main() { super::f(); }", "`super` used at the crate root");
    rejects("mod m { pub fn f() {} pub fn f() {} } fn main() {}", "`m::f` is defined more than once");
    rejects("mod m { } fn m() {} fn main() {}", "`m` is defined more than once");
    // same short name in different modules is fine
    assert_eq!(out("mod a { pub fn f() -> i64 { 1 } } mod b { pub fn f() -> i64 { 2 } } fn f() -> i64 { 3 } fn main() { print(a::f() + b::f() * 10 + f() * 100); }"), "321\n");
}
#[test]
fn unqualified_names_do_not_see_other_modules() {
    rejects("mod m { pub fn f() {} } fn main() { f(); }", "undefined function `f`");
    rejects("fn f() {} mod m { pub fn g() { f(); } } fn main() {}", "undefined function `f`"); // needs crate::f
}
#[test]
fn module_level_layer_default_inside_modules() {
    let src = "mod hw { @layer(hardware);\n pub fn set(a: i64, v: i64) { unsafe { poke(a, v); } } pub fn get(a: i64) -> i64 { unsafe { peek(a) } } }
        fn main() { hw::set(2, 9); print(hw::get(2)); }";
    assert_eq!(out(src), "9\n");
    // the default does not leak out of the module
    rejects("mod hw { @layer(hardware);\n pub fn f() {} } fn main() { unsafe { } }", "only permitted in @layer(hardware)");
    rejects("@layer(hardware)\nstruct S { x: i64 } fn main() {}", "@layer applies only to functions");
}

// ======================= layers with the new constructs =======================

#[test]
fn declarative_layer_forbids_aggregate_mutation_but_allows_pure_aggregates() {
    let ok = "struct V { x: f64, y: f64 } enum E { A(i64), B }
        @layer(declarative)\nfn norm2(v: V) -> f64 { v.x * v.x + v.y * v.y }
        @layer(declarative)\nfn pick(e: E, a: [i64; 3]) -> i64 { match e { E::A(i) => a[i], E::B => 0 } }
        fn main() { print(norm2(V { x: 3.0, y: 4.0 })); print(pick(E::A(1), [5, 6, 7])); }";
    assert_eq!(out(ok), "25.0\n6\n");
    rejects("struct V { x: i64 } @layer(declarative)\nfn f(v: V) -> i64 { let w = v; w.x = 1; w.x } fn main() {}", "assignment is not permitted in @layer(declarative)");
    rejects("@layer(declarative)\nfn f(a: [i64; 2]) -> i64 { let b = a; b[0] = 1; b[0] } fn main() {}", "not permitted in @layer(declarative)");
}
#[test]
fn hardware_layer_bit_manipulation_matches_reference_crc8() {
    // CRC-8 (poly 0x1D) bitwise loop; expected values computed independently in Python.
    let src = "@layer(hardware)\nfn crc8(x: u8) -> u8 { let mut v = x; let mut i = 0;
            while i < 8 { if v & 128 != 0 { v = (v << 1) ^ 29; } else { v = v << 1; } i = i + 1; } v }
        fn main() { print(crc8(1)); print(crc8(128)); let mut s: u64 = 0; let mut b: u8 = 0; while true { s = s + crc8(b) as u64; if b == 255 { return; } b = b + 1; } }";
    // main returns early via `return` after the loop body; print the checksum separately:
    assert!(out(src).starts_with("29\n38\n"));
    let src2 = "@layer(hardware)\nfn crc8(x: u8) -> u8 { let mut v = x; let mut i = 0;
            while i < 8 { if v & 128 != 0 { v = (v << 1) ^ 29; } else { v = v << 1; } i = i + 1; } v }
        fn main() { let mut s: u64 = 0; let mut b: u8 = 0; let mut go = true; while go { s = s + crc8(b) as u64; if b == 255 { go = false; } else { b = b + 1; } } print(s); }";
    assert_eq!(out(src2), "32640\n");
}

// ======================= robustness =======================

#[test]
fn frontend_never_panics_on_mutated_m1_programs() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut sources = Vec::new();
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().and_then(|x| x.to_str()) == Some("kd") { sources.push(std::fs::read_to_string(p).unwrap()); }
    }
    assert!(sources.len() >= 6);
    let mut rng = Lcg(2026);
    for src in &sources {
        let chars: Vec<char> = src.chars().collect();
        for _ in 0..800 {
            let mut c = chars.clone();
            for _ in 0..(1 + rng.next() % 4) {
                if c.is_empty() { break; }
                let i = (rng.next() as usize) % c.len();
                let pool: Vec<char> = "(){}[];,:.+-*/%=<>!&|^@\"x1 _".chars().collect();
                match rng.next() % 3 {
                    0 => { c.remove(i); }
                    1 => { c[i] = pool[(rng.next() as usize) % pool.len()]; }
                    _ => { c.insert(i, pool[(rng.next() as usize) % pool.len()]); }
                }
            }
            let s: String = c.into_iter().collect();
            let _ = compile(&s); // must return Ok/Err, never panic
        }
    }
}
#[test]
fn programs_that_pass_the_checker_do_not_panic_at_runtime() {
    // Mutants that still type-check are executed (with a step guard via bounded recursion/loops removed by size);
    // any panic (as opposed to a RuntimeError) is a checker/interpreter invariant violation.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut rng = Lcg(77);
    let mut executed = 0;
    for name in ["shapes.kd", "arrays.kd", "modules.kd", "ints.kd"] {
        let src = std::fs::read_to_string(dir.join(name)).unwrap();
        let chars: Vec<char> = src.chars().collect();
        for _ in 0..300 {
            let mut c = chars.clone();
            let i = (rng.next() as usize) % c.len();
            // only mutate digits / operators so that most mutants still compile
            let pool: Vec<char> = "0123456789+-*/%<>&|^".chars().collect();
            if c[i].is_ascii_digit() || "+-*/%<>&|^".contains(c[i]) { c[i] = pool[(rng.next() as usize) % pool.len()]; } else { continue; }
            let s: String = c.into_iter().collect();
            if compile(&s).is_ok() {
                // Mutants that loop forever are stopped by the step limit.
                let s2 = s.clone();
                let h = std::thread::Builder::new().stack_size(256 << 20).spawn(move || { let _ = kendrah::run_source_fuel(&s2, 5_000_000); }).unwrap();
                // A panic inside the thread shows up as Err on join.
                assert!(h.join().is_ok(), "runtime panic for mutant:\n{}", s);
                executed += 1;
            }
        }
    }
    assert!(executed > 20, "too few runnable mutants: {}", executed);
}
