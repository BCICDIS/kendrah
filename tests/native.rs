//! M3: native backend (x86-64 Linux via clang). Every program is run on the UIR interpreter AND as a native
//! executable; stdout, exit status and the full located runtime error must agree (`run_native_differential`).
use kendrah::native::{emit_llvm, run_native_differential};
use kendrah::RunError;

fn ok(src: &str) -> String {
    match run_native_differential(src, 1) {
        Ok(o) => o,
        Err(e) => panic!("{:?}\n{}", e, src),
    }
}

/// The program must fail at runtime identically in both engines; returns the message.
fn rt_err(src: &str) -> String {
    match run_native_differential(src, 1) {
        Err(RunError::Runtime(e)) => e.message,
        other => panic!("expected runtime error, got {:?}\n{}", other, src),
    }
}

#[test]
fn examples_match_recorded_output() {
    for name in ["fib", "primes", "layers", "shapes", "arrays", "modules", "ints", "refs", "strings", "generic_types", "vec_sieve", "methods", "owned_enums", "boxes"] {
        let src = std::fs::read_to_string(format!("examples/{}.kd", name)).unwrap();
        let want = std::fs::read_to_string(format!("examples/{}.out", name)).unwrap();
        assert_eq!(ok(&src), want, "example {}", name);
    }
}

#[test]
fn optimisation_levels_agree() {
    let src = std::fs::read_to_string("examples/primes.kd").unwrap();
    for o in [0u8, 2, 3] {
        let n = kendrah::native::run_native(&src, "t.kd", o).unwrap();
        assert_eq!(n.stdout, std::fs::read_to_string("examples/primes.out").unwrap(), "-O{}", o);
        assert_eq!(n.code, 0);
    }
}

#[test]
fn scalars_and_control_flow() {
    assert_eq!(ok("fn main() { print(1 + 2 * 3); print(true); print(\"hi\"); print(7 / 2); print(-7 % 3); }"), "7\ntrue\nhi\n3\n-1\n");
    assert_eq!(ok("fn main() { let mut i = 0; let mut s = 0; while i < 10 { if i % 2 == 0 { s = s + i; } i = i + 1; } print(s); }"), "20\n");
    assert_eq!(ok("fn f(n: i64) -> i64 { if n <= 1 { return 1; } n * f(n - 1) } fn main() { print(f(20)); }"), "2432902008176640000\n");
    assert_eq!(ok("fn main() { let a = true && false || true; print(a); print(!a); print(1 < 2 && 2 < 3); }"), "true\nfalse\ntrue\n");
    assert_eq!(ok("fn main() { let x = 5; let x = x + 1; { let x = 100; print(x); } print(x); }"), "100\n6\n");
}

#[test]
fn strings() {
    assert_eq!(ok("fn main() { let a = \"héllo \\\"q\\\"\"; print(a); print(a == \"héllo \\\"q\\\"\"); print(a != \"x\"); print(\"\" == \"\"); }"), "héllo \"q\"\ntrue\ntrue\ntrue\n");
}

#[test]
fn floats_format_like_the_interpreter() {
    let vals = ["0.0", "1.0", "0.1", "0.3", "100.0", "123456789.125", "1.5", "0.0001", "0.00001234", "9999999999999998.0",
        "10000000000000000.0", "123456789012345680000.0", "3.141592653589793", "1000000.0 * 1000000.0 * 1000.0", "1.0 / 4000000.0", "0.5", "299792458.0"];
    let mut body = String::new();
    for v in vals { body.push_str(&format!("print({}); print(-{}); print({} / 3.0);\n", v, v, v)); }
    body.push_str("let z = 0.0; print(z / z); print(1.0 / z); print(-1.0 / z); print(-z); print(1.0 % 0.3); print(7.5 % -2.0);\n");
    body.push_str("print(1.0 < 2.0); print(0.0 / 0.0 == 0.0 / 0.0); print(0.0 / 0.0 != 0.0 / 0.0); print(2.0 >= 2.0);\n");
    ok(&format!("fn main() {{ {} }}", body));
}

#[test]
fn float_casts_saturate_and_wrap_like_the_interpreter() {
    let mut body = String::new();
    for v in ["0.0", "1.9", "-1.9", "255.5", "256.0", "-129.0", "10000000000.0", "-10000000000.0", "9223372036854775807.0", "18446744073709551616.0", "0.0 / 0.0", "1.0 / 0.0", "-1.0 / 0.0"] {
        for t in ["i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64"] {
            body.push_str(&format!("print(({}) as {});\n", v, t));
        }
    }
    for t in ["i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64"] {
        body.push_str(&format!("let a: {t} = 100; print(a as f64); print(a as i8); print(a as u64); print((a as i8) as u32);\n"));
    }
    body.push_str("let m: i64 = -1; print(m as u8); print(m as u64); print(m as f64); print(true as i32); print(false as u8);\n");
    ok(&format!("fn main() {{ {} }}", body));
}

#[test]
fn integer_semantics_per_type() {
    for (t, vals) in [
        ("i8", vec!["-128", "-127", "-1", "0", "1", "63", "127"]),
        ("u8", vec!["0", "1", "2", "127", "128", "254", "255"]),
        ("i16", vec!["-32768", "-1", "0", "1", "255", "32767"]),
        ("u16", vec!["0", "1", "255", "32768", "65535"]),
        ("i32", vec!["-2147483648", "-1", "0", "1", "65536", "2147483647"]),
        ("u32", vec!["0", "1", "65536", "2147483648", "4294967295"]),
        ("i64", vec!["-9223372036854775808", "-1", "0", "1", "4294967296", "9223372036854775807"]),
        ("u64", vec!["0", "1", "4294967296", "9223372036854775808", "18446744073709551615"]),
    ] {
        // Each (op, a, b) is its own tiny program so a runtime error in one case does not hide the others.
        // Cases are batched into one *passing* program per op where no error occurs, and errors are tested singly.
        let mut passing = String::new();
        let mut failing: Vec<String> = Vec::new();
        for a in &vals { for b in &vals {
            for op in ["+", "-", "*", "/", "%", "&", "|", "^", "<", "<=", ">", ">=", "==", "!="] {
                let stmt = format!("let a: {t} = {a}; let b: {t} = {b}; print(a {op} b);\n");
                let single = format!("fn main() {{ {} }}", stmt);
                // The interpreter decides whether it errors; keep passing ones batched.
                let mut buf = Vec::new();
                let u = kendrah::compile_uir(&single).unwrap();
                if kendrah::uir_interp::run(&u, &mut buf, None).is_ok() {
                    passing.push_str(&format!("{{ {} }}\n", stmt));
                } else { failing.push(single); }
            }
        }}
        ok(&format!("fn main() {{ {} }}", passing));
        for f in failing.iter().step_by(7) { rt_err(f); } // sample of every error class per type
        // shifts, negation, casts between all pairs
        let mut sh = String::new();
        for a in &vals { for n in [0u32, 1, 3, 7] { sh.push_str(&format!("{{ let a: {t} = {a}; print(a << {n}); print(a >> {n}); }}\n")); } }
        for a in &vals { sh.push_str(&format!("{{ let a: {t} = {a}; print(a as i8); print(a as u8); print(a as i16); print(a as u16); print(a as i32); print(a as u32); print(a as i64); print(a as u64); print(a as f64); }}\n")); }
        ok(&format!("fn main() {{ {} }}", sh));
    }
}

#[test]
fn integer_error_classes_have_identical_messages() {
    assert_eq!(rt_err("fn main() { let a: i32 = 2147483647; print(a + 1); }"), "integer overflow in addition (i32)");
    assert_eq!(rt_err("fn main() { let a: u8 = 0; print(a - 1); }"), "integer overflow in subtraction (u8)");
    assert_eq!(rt_err("fn main() { let a: i64 = 4611686018427387904; print(a * 2); }"), "integer overflow in multiplication (i64)");
    assert_eq!(rt_err("fn main() { let a: i8 = -128; print(-a); }"), "integer overflow in negation (i8)");
    assert_eq!(rt_err("fn main() { let z = 0; print(1 / z); }"), "division by zero");
    assert_eq!(rt_err("fn main() { let z = 0; print(1 % z); }"), "remainder by zero");
    assert_eq!(rt_err("fn main() { let a: i16 = -32768; let m: i16 = -1; print(a / m); }"), "integer overflow in division (i16)");
    assert_eq!(rt_err("fn main() { let a: i16 = -32768; let m: i16 = -1; print(a % m); }"), "integer overflow in remainder (i16)");
    assert_eq!(rt_err("fn main() { let a: u32 = 1; let n: u8 = 32; print(a << n); }"), "shift amount 32 out of range for u32 (valid: 0..32)");
    assert_eq!(rt_err("fn main() { let a: i64 = 1; let n: i8 = -1; print(a >> n); }"), "shift amount -1 out of range for i64 (valid: 0..64)");
    assert_eq!(rt_err("fn main() { let a: u8 = 1; let n: u64 = 18446744073709551615; print(a << n); }"), "shift amount 18446744073709551615 out of range for u8 (valid: 0..8)");
    // output produced before the error must still appear
    assert_eq!(rt_err("fn main() { print(1); print(2); let z = 0; print(1 / z); print(3); }"), "division by zero");
}

#[test]
fn arrays_bounds_and_value_semantics() {
    assert_eq!(ok("fn main() { let mut a = [1, 2, 3]; let b = a; a[0] = 99; print(a[0]); print(b[0]); print(len(a)); }"), "99\n1\n3\n");
    assert_eq!(ok("fn f(p: [i64; 3]) -> i64 { let mut a = p; a[0] = 100; a[0] + a[1] } fn main() { let x = [1, 2, 3]; print(f(x)); print(x[0]); }"), "102\n1\n");
    assert_eq!(ok("fn mk() -> [i64; 4] { [4, 3, 2, 1] } fn main() { let a = mk(); print(a[0] * 10 + a[3]); }"), "41\n");
    assert_eq!(ok("fn main() { let mut g = [[0; 3]; 2]; g[1][2] = 7; g[0][0] = 1; let h = g; g[1][2] = 8; print(h[1][2]); print(g[1][2]); print(g[0][0]); print(h[0][1]); }"), "7\n8\n1\n0\n");
    assert_eq!(ok("fn main() { let a = [0; 0]; print(len(a)); let f = [1.5; 3]; print(f[2]); let b = [true; 2]; print(b[1]); let s = [\"a\"; 2]; print(s[1]); }"), "0\n1.5\ntrue\na\n");
    assert_eq!(ok("fn main() { let mut a = [0; 100000]; let mut i = 0; while i < len(a) { a[i] = i * 2; i = i + 1; } print(a[99999]); }"), "199998\n");
    assert_eq!(rt_err("fn main() { let a = [1, 2, 3]; let i = 3; print(a[i]); }"), "array index out of bounds: the index is 3 but the length is 3");
    assert_eq!(rt_err("fn main() { let a = [1, 2, 3]; let i: i8 = -1; print(a[i]); }"), "array index out of bounds: the index is -1 but the length is 3");
    assert_eq!(rt_err("fn main() { let a = [1, 2, 3]; let i: u64 = 18446744073709551615; print(a[i]); }"), "array index out of bounds: the index is 18446744073709551615 but the length is 3");
    assert_eq!(rt_err("fn main() { let mut g = [[0; 3]; 2]; let i = 1; let j = 5; g[i][j] = 1; }"), "array index out of bounds: the index is 5 but the length is 3");
}

#[test]
fn structs_enums_and_match() {
    assert_eq!(ok("struct P { x: i64, y: f64, ok: bool, n: str } fn main() { let mut p = P { n: \"s\", ok: true, y: 2.5, x: 4 }; p.x = p.x + 1; let q = p; p.y = 0.5; print(q.x); print(q.y); print(p.y); print(q.ok); print(q.n); }"), "5\n2.5\n0.5\ntrue\ns\n");
    assert_eq!(ok("struct In { a: u8 } struct Out { i: In, arr: [In; 2] } fn main() { let mut o = Out { i: In { a: 1 }, arr: [In { a: 2 }, In { a: 3 }] }; o.arr[1].a = 9; o.i.a = 7; let c = o; o.i.a = 0; print(c.i.a); print(c.arr[1].a); print(o.i.a); }"), "7\n9\n0\n");
    assert_eq!(ok("enum E { A, B(i64), C(i64, f64), D([i64; 2]) } fn f(e: E) -> i64 { match e { E::A => 0, E::B(x) => x, E::C(a, _) => a * 2, E::D(arr) => arr[0] + arr[1] } } fn main() { print(f(E::A)); print(f(E::B(5))); print(f(E::C(7, 1.0))); print(f(E::D([20, 22]))); }"), "0\n5\n14\n42\n");
    assert_eq!(ok("enum Op { Add(i64, i64), Neg(i64) } enum R { Ok(i64), Err(str) } fn run(o: Op) -> R { match o { Op::Add(a, b) => R::Ok(a + b), Op::Neg(a) => if a == 0 { R::Err(\"zero\") } else { R::Ok(0 - a) } } } fn main() { match run(Op::Add(2, 3)) { R::Ok(v) => print(v), R::Err(m) => print(m) } match run(Op::Neg(0)) { R::Ok(v) => print(v), R::Err(m) => print(m) } match run(Op::Neg(4)) { R::Ok(v) => print(v), R::Err(m) => print(m) } }"), "5\nzero\n-4\n");
    assert_eq!(ok("fn main() { let n = 3; let s = match n { 1 => \"one\", 3 => \"three\", _ => \"many\" }; print(s); let b = match true { true => 1, false => 0 }; print(b); let t = match \"x\" { \"y\" => 1, \"x\" => 2, _ => 3 }; print(t); }"), "three\n1\n2\n");
}

#[test]
fn recursion_depth_rule_is_identical() {
    assert_eq!(ok("fn d(n: i64) -> i64 { if n == 0 { 0 } else { 1 + d(n - 1) } } fn main() { print(d(1990)); }"), "1990\n");
    assert!(rt_err("fn d(n: i64) -> i64 { if n == 0 { 0 } else { 1 + d(n - 1) } } fn main() { print(d(5000)); }").starts_with("stack overflow: call depth exceeded 2000"));
    assert!(rt_err("fn f() -> i64 { f() } fn main() { print(f()); }").starts_with("stack overflow"));
}

#[test]
fn modules_layers_and_aggregate_returns() {
    assert_eq!(ok("mod m { pub struct V { a: i64, b: i64 } pub fn mk(a: i64) -> V { V { a: a, b: a * 2 } } pub fn sum(v: V) -> i64 { v.a + v.b } } fn main() { print(m::sum(m::mk(5))); }"), "15\n");
    assert_eq!(ok("@layer(declarative) fn sq(x: i64) -> i64 { x * x } fn main() { print(sq(12)); }"), "144\n");
    // Unused hardware function with peek is not emitted, so it does not block the build.
    assert_eq!(ok("@layer(hardware) fn hw() -> i64 { unsafe { peek(0) } } fn main() { print(1); }"), "1\n");
}

#[test]
fn peek_poke_use_the_simulated_memory_natively() {
    assert_eq!(ok("@layer(hardware) fn main() { unsafe { poke(0, 7); poke(255, 200); print(peek(0) + peek(255)); print(peek(100)); let a: i64 = 3; poke(a, 255); print(peek(3)); poke(a + 1, a); print(peek(4)); } }"), "207\n0\n255\n3\n");
    assert_eq!(rt_err("@layer(hardware) fn main() { unsafe { print(peek(256)); } }"), "memory access out of bounds: address 256 (valid: 0..256)");
    assert_eq!(rt_err("@layer(hardware) fn main() { unsafe { let a = 0 - 1; print(peek(a)); } }"), "memory access out of bounds: address -1 (valid: 0..256)");
    assert_eq!(rt_err("@layer(hardware) fn main() { unsafe { let a: i64 = 9223372036854775807; poke(a, 1); } }"), "memory access out of bounds: address 9223372036854775807 (valid: 0..256)");
    assert_eq!(rt_err("@layer(hardware) fn main() { unsafe { poke(1, 256); } }"), "poke value 256 does not fit in a byte");
    assert_eq!(rt_err("@layer(hardware) fn main() { unsafe { poke(1, 0 - 1); } }"), "poke value -1 does not fit in a byte");
    assert_eq!(rt_err("@layer(hardware) fn main() { unsafe { let v: i64 = 9223372036854775807; poke(1, v); } }"), "poke value 9223372036854775807 does not fit in a byte");
    // the memory is shared across function calls
    assert_eq!(ok("@layer(hardware) fn w(a: i64, v: i64) { unsafe { poke(a, v); } } @layer(hardware) fn r(a: i64) -> i64 { unsafe { peek(a) } } fn main() { w(9, 42); print(r(9)); }"), "42\n");
}

#[test]
fn diverging_code_and_dead_blocks() {
    assert_eq!(ok("fn f(x: i64) -> i64 { if x > 0 { return 1; } else { return 2; } } fn main() { print(f(1)); print(f(-1)); }"), "1\n2\n");
    assert_eq!(ok("fn f() -> i64 { return 3; } fn main() { print(f()); let mut i = 0; while true { i = i + 1; if i == 5 { return; } } print(99); }"), "3\n");
}

fn diag_msgs(src: &str) -> Vec<(u32, u32, String)> {
    let u = kendrah::compile_uir(src).unwrap();
    emit_llvm(&u, "t.kd").err().expect("expected diagnostics").into_iter().map(|d| (d.span.line, d.span.col, d.message)).collect()
}

#[test]
fn unsupported_constructs_are_diagnosed_with_spans_not_miscompiled() {
    let d = diag_msgs("fn main() {\n    let a = \"x\" + \"y\";\n    print(a);\n}");
    assert_eq!(d.len(), 1);
    assert_eq!(d[0].0, 2);
    assert!(d[0].2.contains("concatenation"));
    // transitively reachable
    let d = diag_msgs("fn cat() -> str { \"a\" + \"b\" }\nfn main() { print(cat()); }");
    assert_eq!(d.len(), 1);
}

#[test]
fn emitted_ir_names_the_target_and_is_deterministic() {
    let u = kendrah::compile_uir("fn main() { print(1 + 2); }").unwrap();
    let a = emit_llvm(&u, "t.kd").unwrap();
    let b = emit_llvm(&u, "t.kd").unwrap();
    assert_eq!(a, b);
    assert!(a.contains("target triple = \"x86_64-pc-linux-gnu\""));
    assert!(a.contains("llvm.sadd.with.overflow.i64"));
}

#[test]
fn cli_build_and_diagnose() {
    let exe = env!("CARGO_BIN_EXE_kendrah");
    let dir = std::env::temp_dir().join(format!("kd-cli-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let out = dir.join("fibexe");
    let r = std::process::Command::new(exe).args(["build", "-O1", "-o"]).arg(&out).arg("examples/fib.kd").output().unwrap();
    assert!(r.status.success(), "{}", String::from_utf8_lossy(&r.stderr));
    let run = std::process::Command::new(&out).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), std::fs::read_to_string("examples/fib.out").unwrap());
    // unsupported construct => exit 1, no executable produced
    let bad = dir.join("badexe");
    let cat = dir.join("cat.kd");
    std::fs::write(&cat, "fn main() { print(\"a\" + \"b\"); }").unwrap();
    let r = std::process::Command::new(exe).args(["build", "-o"]).arg(&bad).arg(&cat).output().unwrap();
    assert_eq!(r.status.code(), Some(1));
    assert!(!bad.exists());
    assert!(String::from_utf8_lossy(&r.stderr).contains("not supported by the native backend"));
    // runtime error exit code 2 and located message naming the source file given at build time
    let src = dir.join("boom.kd");
    std::fs::write(&src, "fn main() {\n    let z = 0;\n    print(1 / z);\n}\n").unwrap();
    let boom = dir.join("boom");
    assert!(std::process::Command::new(exe).args(["build", "-o"]).arg(&boom).arg(&src).status().unwrap().success());
    let run = std::process::Command::new(&boom).output().unwrap();
    assert_eq!(run.status.code(), Some(2));
    assert_eq!(String::from_utf8_lossy(&run.stderr), format!("{}:3:13: runtime error: division by zero\n", src.display()));
    // emit-llvm works
    let r = std::process::Command::new(exe).args(["emit-llvm", "examples/fib.kd"]).output().unwrap();
    assert!(r.status.success() && String::from_utf8_lossy(&r.stdout).contains("define"));
    let _ = std::fs::remove_dir_all(&dir);
}
