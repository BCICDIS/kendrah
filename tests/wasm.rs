//! M5: wasm32 backend (target T2: freestanding module + Node.js host). Every program is run on the UIR interpreter
//! AND as a wasm module under Node; stdout, exit status and the full located runtime error must agree.
use kendrah::native::run_wasm_differential;
use kendrah::RunError;

fn ok(src: &str) -> String {
    match run_wasm_differential(src, 1) {
        Ok(o) => o,
        Err(e) => panic!("{:?}\n{}", e, src),
    }
}
fn rt_err(src: &str) -> String {
    match run_wasm_differential(src, 1) {
        Err(RunError::Runtime(e)) => e.message,
        other => panic!("expected runtime error, got {:?}\n{}", other, src),
    }
}

#[test]
fn examples_match_recorded_output() {
    for name in ["fib", "primes", "layers", "shapes", "arrays", "modules", "ints", "refs", "strings", "generic_types", "vec_sieve", "methods"] {
        let src = std::fs::read_to_string(format!("examples/{}.kd", name)).unwrap();
        let want = std::fs::read_to_string(format!("examples/{}.out", name)).unwrap();
        assert_eq!(ok(&src), want, "example {}", name);
    }
}

#[test]
fn optimisation_levels_agree() {
    let src = std::fs::read_to_string("examples/primes.kd").unwrap();
    for o in [0u8, 2, 3] {
        let n = kendrah::native::run_wasm(&src, "t.kd", o).unwrap();
        assert_eq!(n.stdout, std::fs::read_to_string("examples/primes.out").unwrap(), "-O{}", o);
        assert_eq!(n.code, 0);
    }
}

#[test]
fn scalars_strings_and_control_flow() {
    assert_eq!(ok("fn main() { print(1 + 2 * 3); print(true); print(\"hi\"); print(7 / 2); print(-7 % 3); }"), "7\ntrue\nhi\n3\n-1\n");
    assert_eq!(ok("fn f(n: i64) -> i64 { if n <= 1 { return 1; } n * f(n - 1) } fn main() { print(f(20)); }"), "2432902008176640000\n");
    assert_eq!(ok("fn main() { let a = \"héllo \\\"q\\\"\"; print(a); print(a == \"héllo \\\"q\\\"\"); print(a != \"x\"); }"), "héllo \"q\"\ntrue\ntrue\n");
    assert_eq!(ok("fn main() { let mut i = 0; let mut s = 0; while i < 10 { if i % 2 == 0 { s = s + i; } i = i + 1; } print(s); }"), "20\n");
}

#[test]
fn floats_format_like_the_interpreter() {
    let vals = ["0.0", "1.0", "0.1", "0.3", "100.0", "123456789.125", "1.5", "0.0001", "0.00001234", "9999999999999998.0",
        "10000000000000000.0", "123456789012345680000.0", "3.141592653589793", "1000000.0 * 1000000.0 * 1000.0", "1.0 / 4000000.0", "0.5", "299792458.0"];
    let mut body = String::new();
    for v in vals { body.push_str(&format!("print({}); print(-{}); print({} / 3.0);\n", v, v, v)); }
    body.push_str("let z = 0.0; print(z / z); print(1.0 / z); print(-1.0 / z); print(-z); print(1.0 % 0.3); print(7.5 % -2.0);\n");
    body.push_str("print(1.0 < 2.0); print(0.0 / 0.0 == 0.0 / 0.0); print(2.0 >= 2.0);\n");
    ok(&format!("fn main() {{ {} }}", body));
}

#[test]
fn float_casts_and_integer_types() {
    let mut body = String::new();
    for v in ["0.0", "1.9", "-1.9", "255.5", "256.0", "-129.0", "10000000000.0", "9223372036854775807.0", "18446744073709551616.0", "0.0 / 0.0", "1.0 / 0.0", "-1.0 / 0.0"] {
        for t in ["i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64"] { body.push_str(&format!("print(({}) as {});\n", v, t)); }
    }
    let mut ints = String::new();
    for (t, vals) in [("i8", vec!["-128", "-1", "0", "127"]), ("u32", vec!["0", "65536", "4294967295"]), ("i64", vec!["-9223372036854775808", "-1", "0", "9223372036854775807"]), ("u64", vec!["0", "9223372036854775808", "18446744073709551615"])] {
        for a in &vals {
            ints.push_str(&format!("{{ let a: {t} = {a}; print(a & 85); print(a ^ 1); print(a << 3); print(a >> 2); print(a as i8); print(a as u64); print(a as f64); print(a < 5); }}\n"));
        }
    }
    ok(&format!("fn main() {{ {} {} }}", body, ints));
}

#[test]
fn runtime_errors_have_identical_messages() {
    assert_eq!(rt_err("fn main() { let a: i32 = 2147483647; print(a + 1); }"), "integer overflow in addition (i32)");
    assert_eq!(rt_err("fn main() { let a: u8 = 0; print(a - 1); }"), "integer overflow in subtraction (u8)");
    assert_eq!(rt_err("fn main() { let a: i64 = 4611686018427387904; print(a * 2); }"), "integer overflow in multiplication (i64)");
    assert_eq!(rt_err("fn main() { let z = 0; print(1 / z); }"), "division by zero");
    assert_eq!(rt_err("fn main() { let a: u32 = 1; let n: u8 = 32; print(a << n); }"), "shift amount 32 out of range for u32 (valid: 0..32)");
    assert_eq!(rt_err("fn main() { let a: u8 = 1; let n: u64 = 18446744073709551615; print(a << n); }"), "shift amount 18446744073709551615 out of range for u8 (valid: 0..8)");
    assert_eq!(rt_err("fn main() { let a = [1, 2, 3]; let i = 3; print(a[i]); }"), "array index out of bounds: the index is 3 but the length is 3");
    assert_eq!(rt_err("fn main() { let a = [1, 2, 3]; let i: i8 = -1; print(a[i]); }"), "array index out of bounds: the index is -1 but the length is 3");
    assert_eq!(rt_err("fn f(n: i64) -> i64 { f(n + 1) } fn main() { print(f(0)); }"), "stack overflow: call depth exceeded 2000");
    // output produced before the error still appears
    assert_eq!(rt_err("fn main() { print(1); print(2); let z = 0; print(1 / z); print(3); }"), "division by zero");
}

#[test]
fn aggregates_enums_and_references() {
    assert_eq!(ok("fn main() { let mut g = [[0; 3]; 2]; g[1][2] = 7; let h = g; g[1][2] = 8; print(h[1][2]); print(g[1][2]); }"), "7\n8\n");
    assert_eq!(ok("enum S { C(i64), R(i64, i64), E } fn area(s: S) -> i64 { match s { S::C(r) => r * r * 3, S::R(w, h) => w * h, S::E => 0 } } fn main() { print(area(S::C(2))); print(area(S::R(3, 4))); print(area(S::E)); }"), "12\n12\n0\n");
    assert_eq!(ok("struct P { x: i64, y: i64 } fn bump(p: &mut P) { p.x = p.x + 1; } fn main() { let mut p = P { x: 1, y: 2 }; bump(&mut p); bump(&mut p); print(p.x + p.y); }"), "5\n");
}

#[test]
fn owned_values_strings_vecs_structs_and_methods() {
    assert_eq!(ok("fn main() { let a = string_from(\"foo\"); let b = string_from(\"bar\"); let c = string_concat(&a, &b); print(&c); print(string_len(&c)); let mut s = string_from(\"a\"); string_push(&mut s, \"bc\"); print(&s); print(string_eq(&a, &b)); }"), "foobar\n6\nabc\nfalse\n");
    assert_eq!(ok("fn main() { let mut v: Vec<i64> = vec_new(); for i in 0..1000 { v.push(i * 2); } let mut s = 0; for i in 0..v.len() { s = s + v[i]; } print(s); print(v.pop()); let w = v.clone(); print(w.len()); let mut b: Vec<bool> = vec_new(); b.push(true); print(b[0]); let mut f: Vec<f64> = vec_new(); f.push(1.5); print(f[0]); }"), "999000\n1998\n999\ntrue\n1.5\n");
    assert_eq!(ok("struct Person { name: String, scores: Vec<i64> } impl Person { fn new(n: str) -> Person { let s: Vec<i64> = vec_new(); Person { name: string_from(n), scores: s } } fn add(&mut self, v: i64) { self.scores.push(v); } fn count(&self) -> i64 { self.scores.len() } } fn main() { let mut i = 0; while i < 50 { let mut p = Person::new(\"alice\"); p.add(i); p.add(2); i = i + 1; if i == 49 { print(p.count()); print(&p.name); } } }"), "2\nalice\n");
    assert_eq!(rt_err("fn main() { let mut v: Vec<i64> = vec_new(); v.push(1); print(v[5]); }"), "vector index out of bounds: the index is 5 but the length is 1");
    assert_eq!(rt_err("fn main() { let mut v: Vec<u8> = vec_new(); print(v.pop()); }"), "pop from an empty Vec");
}

#[test]
fn generics_and_memory_growth() {
    assert_eq!(ok("fn id<T>(x: T) -> T { x } enum Opt<T> { Some(T), None } impl<T> Opt<T> { fn unwrap_or(self, d: T) -> T { match self { Opt::Some(v) => v, Opt::None => d } } } fn main() { print(id(5)); print(id(2.5)); print(Opt::Some(3).unwrap_or(0)); }"), "5\n2.5\n3\n");
    // forces the allocator to grow linear memory well past the initial 32 MiB
    assert_eq!(ok("fn main() { let mut v: Vec<i64> = vec_new(); for i in 0..6000000 { v.push(i); } print(v.len()); print(v[5999999]); }"), "6000000\n5999999\n");
    // freed blocks are reused (no unbounded growth) and nothing leaks
    assert_eq!(ok("fn main() { let mut i = 0; while i < 200000 { let s = string_from(\"abcdefgh\"); i = i + 1; } print(i); }"), "200000\n");
}
