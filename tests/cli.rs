//! End-to-end tests of the `kendrah` binary: exit codes, stdout/stderr, diagnostics format.
use std::io::Write;
use std::process::{Command, Output};

fn bin() -> Command { Command::new(env!("CARGO_BIN_EXE_kendrah")) }

fn tmp(name: &str, src: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("kendrah-cli-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let p = dir.join(name);
    std::fs::File::create(&p).unwrap().write_all(src.as_bytes()).unwrap();
    p
}
fn s(o: &[u8]) -> String { String::from_utf8_lossy(o).into_owned() }
fn run(args: &[&str]) -> Output { bin().args(args).output().unwrap() }

#[test]
fn run_prints_program_output_and_exits_zero() {
    let p = tmp("ok.kd", "fn main() { print(40 + 2); }");
    let o = run(&["run", p.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(0));
    assert_eq!(s(&o.stdout), "42\n");
}
#[test]
fn check_ok_exits_zero_without_running() {
    let p = tmp("chk.kd", "fn main() { print(1); }");
    let o = run(&["check", p.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(0));
    assert!(s(&o.stdout).contains(": ok"));
    assert!(!s(&o.stdout).starts_with("1"));
}
#[test]
fn compile_errors_exit_one_with_located_diagnostics_on_stderr() {
    let p = tmp("bad.kd", "fn main() {\n  print(nope);\n}\n");
    let o = run(&["run", p.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(1));
    let e = s(&o.stderr);
    assert!(e.contains("bad.kd:2:9: error: undefined variable `nope`"), "{}", e);
    assert!(e.contains("1 error(s)"), "{}", e);
    assert_eq!(s(&o.stdout), "");
}
#[test]
fn runtime_errors_exit_two_after_partial_output() {
    let p = tmp("rt.kd", "fn main() { print(1); let z = 0; print(1 / z); }");
    let o = run(&["run", p.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2));
    assert_eq!(s(&o.stdout), "1\n");
    assert!(s(&o.stderr).contains("runtime error: division by zero"), "{}", s(&o.stderr));
}
#[test]
fn usage_and_io_errors_exit_64() {
    assert_eq!(run(&[]).status.code(), Some(64));
    assert_eq!(run(&["build", "x.kd"]).status.code(), Some(64));
    assert_eq!(run(&["run", "/definitely/not/here.kd"]).status.code(), Some(64));
}
#[test]
fn every_example_runs_through_the_binary() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut n = 0;
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().and_then(|x| x.to_str()) != Some("kd") { continue; }
        let o = run(&["run", p.to_str().unwrap()]);
        assert_eq!(o.status.code(), Some(0), "{:?}: {}", p, s(&o.stderr));
        assert_eq!(s(&o.stdout), std::fs::read_to_string(p.with_extension("out")).unwrap(), "{:?}", p);
        n += 1;
    }
    assert!(n >= 7);
}

#[test]
fn uir_engine_matches_hir_engine_on_every_example() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().and_then(|x| x.to_str()) != Some("kd") { continue; }
        let a = run(&["run", "--engine", "hir", p.to_str().unwrap()]);
        let b = run(&["run", "--engine", "uir", p.to_str().unwrap()]);
        assert_eq!(a.status.code(), Some(0));
        assert_eq!(b.status.code(), Some(0), "{:?}: {}", p, s(&b.stderr));
        assert_eq!(s(&a.stdout), s(&b.stdout), "{:?}", p);
    }
}
#[test]
fn fuel_flag_stops_infinite_loops_with_exit_two() {
    let p = tmp("loop.kd", "fn main() { while true { } }");
    for eng in ["hir", "uir"] {
        let o = run(&["run", "--engine", eng, "--fuel", "5000", p.to_str().unwrap()]);
        assert_eq!(o.status.code(), Some(2), "{}", eng);
        assert!(s(&o.stderr).contains("step limit"), "{}", s(&o.stderr));
    }
}
#[test]
fn dump_uir_prints_functions_and_bad_flags_are_usage_errors() {
    let p = tmp("d.kd", "fn main() { print(1); }");
    let o = run(&["dump-uir", p.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(0));
    assert!(s(&o.stdout).starts_with("fn #0 main() -> () @layer(application) {"), "{}", s(&o.stdout));
    assert_eq!(run(&["run", "--engine", "bogus", p.to_str().unwrap()]).status.code(), Some(64));
    assert_eq!(run(&["run", "--fuel", "x", p.to_str().unwrap()]).status.code(), Some(64));
    assert_eq!(run(&["check", "--engine", "uir", p.to_str().unwrap()]).status.code(), Some(64));
}

#[test]
fn build_wasm_target_produces_a_runnable_module() {
    let p = tmp("w.kd", "fn main() { print(6 * 7); }");
    let out = p.with_extension("wasm");
    let o = run(&["build", "--target", "wasm32", "-o", out.to_str().unwrap(), p.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(0), "{}", s(&o.stderr));
    let bytes = std::fs::read(&out).unwrap();
    assert_eq!(&bytes[..4], b"\0asm");
    let host = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime/kd_wasm_host.js");
    let r = Command::new("node").arg(host).arg(&out).output().unwrap();
    assert_eq!(s(&r.stdout), "42\n");
    let ll = run(&["emit-llvm", "--target", "wasm32", p.to_str().unwrap()]);
    assert!(s(&ll.stdout).contains("wasm32-unknown-unknown"));
}
