//! C interop (M6): `extern fn` imports, `export fn` C-ABI exports, and their static rules.
use std::io::Write;
use std::process::{Command, Output};

fn bin() -> Command { Command::new(env!("CARGO_BIN_EXE_kendrah")) }
fn s(o: &[u8]) -> String { String::from_utf8_lossy(o).into_owned() }

fn dir(tag: &str) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let d = std::env::temp_dir().join(format!("kendrah-ffi-{}-{}-{}", std::process::id(), tag, N.fetch_add(1, Ordering::SeqCst)));
    std::fs::create_dir_all(&d).unwrap();
    d
}
fn write(d: &std::path::Path, name: &str, src: &str) -> String {
    let p = d.join(name);
    std::fs::File::create(&p).unwrap().write_all(src.as_bytes()).unwrap();
    p.to_str().unwrap().to_string()
}
fn check(src: &str) -> Output {
    let d = dir("chk");
    let p = write(&d, "t.kd", src);
    bin().args(["check", &p]).output().unwrap()
}
fn rejects(src: &str, needle: &str) {
    let o = check(src);
    assert_eq!(o.status.code(), Some(1), "expected rejection of:\n{}\nstderr: {}", src, s(&o.stderr));
    assert!(s(&o.stderr).contains(needle), "missing `{}` in:\n{}", needle, s(&o.stderr));
}
/// Build natively (with optional C sources) and run; returns (stdout, exit code).
fn native(src: &str, c: Option<&str>) -> (String, i32) {
    let d = dir("run");
    let p = write(&d, "t.kd", src);
    let exe = d.join("t").to_str().unwrap().to_string();
    let mut cmd = bin();
    cmd.args(["build", "-o", &exe]);
    if let Some(c) = c { let cp = write(&d, "lib.c", c); cmd.args(["--link", &cp]); }
    cmd.arg(&p);
    let b = cmd.output().unwrap();
    assert_eq!(b.status.code(), Some(0), "build failed: {}", s(&b.stderr));
    let r = Command::new(&exe).output().unwrap();
    (s(&r.stdout), r.status.code().unwrap_or(-1))
}

const LIBC_PROG: &str = r#"
@layer(hardware);
extern fn abs(x: i32) -> i32;
extern fn sqrt(x: f64) -> f64;
fn main() {
    print(unsafe { abs(-41) });
    print(unsafe { sqrt(2.25) });
}
"#;

#[test]
fn calls_libc_functions_natively() {
    assert_eq!(native(LIBC_PROG, None), ("41\n1.5\n".to_string(), 0));
}

#[test]
fn mixed_width_arguments_are_extended_per_the_c_abi() {
    let src = r#"
@layer(hardware);
extern fn c_mix(a: i8, b: u16, c: i64, d: f64) -> f64;
extern fn c_neg8(a: i8) -> i8;
extern fn c_u8(a: u8) -> u8;
fn main() {
    print(unsafe { c_mix(-3, 65535, 1000000000000, 0.5) });
    print(unsafe { c_neg8(-128) });
    print(unsafe { c_u8(255) });
}"#;
    let c = r#"#include <stdint.h>
double c_mix(int8_t a, uint16_t b, int64_t c, double d) { return a + b + (double)c + d; }
int8_t c_neg8(int8_t a) { return (int8_t)(a + 1); }
uint8_t c_u8(uint8_t a) { return (uint8_t)(a - 1); }
"#;
    assert_eq!(native(src, Some(c)), ("1000000065532.5\n-127\n254\n".to_string(), 0));
}

#[test]
fn exported_functions_are_callable_from_c_and_round_trip() {
    let src = r#"
@layer(hardware);
extern fn c_drive(n: i32) -> i64;
extern fn c_note(n: i32);
export fn square(x: i64) -> i64 { x * x }
export fn bump(x: u8) -> u8 { x + 1 }
export fn report(n: i64) { print(n); }
fn main() {
    print(unsafe { c_drive(5) });
    unsafe { c_note(7) };
}"#;
    let c = r#"#include <stdint.h>
long long square(long long);
uint8_t bump(uint8_t);
void report(long long);
int64_t c_drive(int n) { int64_t s = 0; for (int i = 1; i <= n; i++) s += square(i) + bump(250); return s; }
void c_note(int n) { report(n * 6); }
"#;
    assert_eq!(native(src, Some(c)), ("1310\n42\n".to_string(), 0));
}

#[test]
fn unreferenced_export_is_still_emitted() {
    // `main` never calls `twice`; the C side does.
    let src = r#"
@layer(hardware);
extern fn c_twice(x: i32) -> i32;
export fn inc(x: i32) -> i32 { x + 1 }
fn main() { print(unsafe { c_twice(10) }); }"#;
    let c = "int inc(int); int c_twice(int x) { return inc(inc(x)); }\n";
    assert_eq!(native(src, Some(c)), ("12\n".to_string(), 0));
}

#[test]
fn a_runtime_error_inside_an_export_called_from_c_is_reported_with_its_location() {
    let src = r#"
@layer(hardware);
extern fn c_call(x: i32) -> i32;
export fn boom(x: i32) -> i32 { 100 / x }
fn main() { print(unsafe { c_call(0) }); }"#;
    let c = "int boom(int); int c_call(int x) { return boom(x); }\n";
    let d = dir("err");
    let p = write(&d, "t.kd", src);
    let cp = write(&d, "lib.c", c);
    let exe = d.join("t").to_str().unwrap().to_string();
    let b = bin().args(["build", "-o", &exe, "--link", &cp, &p]).output().unwrap();
    assert_eq!(b.status.code(), Some(0), "{}", s(&b.stderr));
    let r = Command::new(&exe).output().unwrap();
    assert_eq!(r.status.code(), Some(2));
    assert!(s(&r.stderr).contains("division by zero"), "{}", s(&r.stderr));
}

#[test]
fn the_interpreters_refuse_to_run_c_calls_with_a_located_error() {
    let d = dir("interp");
    let p = write(&d, "t.kd", LIBC_PROG);
    for engine in ["hir", "uir"] {
        let o = bin().args(["run", "--engine", engine, &p]).output().unwrap();
        assert_eq!(o.status.code(), Some(2), "{}", engine);
        assert!(s(&o.stderr).contains("cannot call the C function `abs` in the interpreter"), "{}", s(&o.stderr));
    }
}

#[test]
fn calling_c_requires_unsafe() {
    rejects("@layer(hardware);\nextern fn abs(x: i32) -> i32;\nfn main() { print(abs(-1)); }", "calling the C function `abs` is unsafe");
}

#[test]
fn unsafe_is_only_available_in_the_hardware_layer_so_c_cannot_be_called_elsewhere() {
    rejects("extern fn abs(x: i32) -> i32;\nfn main() { print(unsafe { abs(-1) }); }", "only permitted in @layer(hardware)");
}

#[test]
fn signatures_must_be_c_abi_safe() {
    rejects("@layer(hardware);\nextern fn f(x: str) -> i32;\nfn main() {}", "not C-ABI safe");
    rejects("@layer(hardware);\nextern fn f(x: bool) -> i32;\nfn main() {}", "not C-ABI safe");
    rejects("@layer(hardware);\nextern fn f(x: i32) -> String;\nfn main() {}", "not C-ABI safe");
    rejects("export fn f(x: [i32; 2]) -> i32 { 0 }\nfn main() {}", "not C-ABI safe");
    rejects("struct P { x: i32 }\nexport fn f(p: P) -> i32 { 0 }\nfn main() {}", "not C-ABI safe");
}

#[test]
fn reserved_and_duplicate_symbol_names_are_rejected() {
    rejects("export fn main() {}", "reserved");
    rejects("export fn kd_x() {}\nfn main() {}", "reserved");
    rejects("export fn f() {}\nexport fn f() {}\nfn main() {}", "defined more than once");
    rejects("mod a { export fn f() {} }\nmod b { export fn f() {} }\nfn main() {}", "more than once");
}

#[test]
fn extern_cannot_be_generic_or_have_a_body_or_live_in_an_impl() {
    rejects("@layer(hardware);\nextern fn f<T>(x: T) -> T;\nfn main() {}", "cannot be generic");
    rejects("@layer(hardware);\nextern fn f(x: i32) -> i32 { x }\nfn main() {}", "no body");
    rejects("struct S { a: i32 }\nimpl S { extern fn f(x: i32) -> i32; }\nfn main() {}", "only `fn` items");
}

#[test]
fn export_requires_a_body() {
    rejects("export fn f(x: i32) -> i32;\nfn main() {}", "expected");
}

#[test]
fn wasm_target_rejects_c_interop_honestly() {
    let d = dir("wasm");
    let p = write(&d, "t.kd", LIBC_PROG);
    let o = bin().args(["build", "--target", "wasm32", "-o", d.join("t.wasm").to_str().unwrap(), &p]).output().unwrap();
    assert_eq!(o.status.code(), Some(1));
    assert!(s(&o.stderr).contains("C interop is not supported on the wasm32 target"), "{}", s(&o.stderr));
}

#[test]
fn export_functions_still_run_in_the_interpreters_as_ordinary_functions() {
    let d = dir("exp");
    let p = write(&d, "t.kd", "export fn sq(x: i64) -> i64 { x * x }\nfn main() { print(sq(12)); }");
    for engine in ["hir", "uir"] {
        let o = bin().args(["run", "--engine", engine, &p]).output().unwrap();
        assert_eq!((o.status.code(), s(&o.stdout)), (Some(0), "144\n".to_string()), "{}", engine);
    }
}
