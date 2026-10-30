//! M2 tests: UIR lowering, verifier (positive and negative), differential agreement of the two engines,
//! operand-spilling around control flow, step limits.
use kendrah::ast::BinOp;
use kendrah::ty::{IntTy, Ty};
use kendrah::uir::*;
use kendrah::{compile, lower, run_differential, run_source_with, Engine, RunError};

fn lowered(src: &str) -> UProgram { lower::lower_program(&compile(src).unwrap_or_else(|e| panic!("{:?}", e))) }

fn run2(src: &str) -> Result<String, RunError> {
    let s = src.to_string();
    std::thread::Builder::new().stack_size(256 << 20).spawn(move || run_differential(&s, None)).unwrap().join().unwrap()
}
fn out(src: &str) -> String { run2(src).unwrap_or_else(|e| panic!("{:?}\n{}", e, src)) }

fn examples() -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut v = Vec::new();
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().and_then(|x| x.to_str()) == Some("kd") {
            v.push((p.file_name().unwrap().to_string_lossy().into_owned(), std::fs::read_to_string(&p).unwrap()));
        }
    }
    v
}

// ---------------------------------------------------------------- lowering + verification

#[test]
fn every_example_lowers_to_verified_uir_and_both_engines_match_expected_output() {
    let ex = examples();
    assert!(ex.len() >= 7);
    for (name, src) in ex {
        verify(&lowered(&src)).unwrap_or_else(|e| panic!("{}: {:?}", name, e));
        let want = std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples").join(name.replace(".kd", ".out"))).unwrap();
        assert_eq!(out(&src), want, "{}", name);
        assert_eq!(run_source_with(&src, Engine::Uir, None).unwrap(), want, "{} (UIR engine alone)", name);
    }
}

#[test]
fn dump_format_snapshot() {
    let u = lowered("fn main() { let x = 1 + 2; print(x); }");
    let want = "fn #0 main() -> () @layer(application) {
  slot $0: i64
 b0:
   %0: i64 = const 1
   %1: i64 = const 2
   %2: i64 = add %0, %1
   store $0, %2
   %3: i64 = load $0
   %4: () = builtin print(%3)
   %5: () = const ()
   ret %5
}
";
    assert_eq!(u.dump(), want);
}

#[test]
fn control_flow_shapes_in_uir() {
    let u = lowered("fn main() { let mut i = 0; while i < 3 { i = i + 1; } }");
    let f = &u.fns[0];
    // entry, loop head, body, exit (+ no dead blocks for a while loop)
    assert_eq!(f.blocks.len(), 4, "{}", u.dump());
    assert!(matches!(f.blocks[1].term, UTerm::CondBr(..)));
    assert_eq!(f.blocks[2].term, UTerm::Br(1), "loop back-edge");
}

#[test]
fn temps_never_cross_blocks_even_when_operands_contain_control_flow() {
    // The classic hazard: an earlier operand is live across a branch in a later operand.
    let src = "
        struct S { a: i64, b: i64 }
        fn add3(a: i64, b: i64, c: i64) -> i64 { a * 100 + b * 10 + c }
        fn main() {
            let c = true; let d = false;
            print(10 + if c { 1 } else { 2 });
            print(10 - if d { 1 } else { 2 });
            let a = [1, 2, 3];
            print(a[if c { 0 } else { 2 }] * 7);
            let g = [[1, 2], [3, 4]];
            print(g[1][if c { 0 } else { 1 }]);
            print(g[if d { 0 } else { 1 }][if c { 1 } else { 0 }]);
            let s = S { a: 5, b: if c { 6 } else { 7 } };
            print(s.a * 10 + s.b);
            print(add3(1, if c { 2 } else { 3 }, match 4 { 4 => 5, _ => 6 }));
            let mut m = [0, 0, 0];
            m[if c { 1 } else { 2 }] = if d { 8 } else { 9 };
            print(m[0] * 100 + m[1] * 10 + m[2]);
            print(1 + (if c { 2 } else { 3 }) * (match d { true => 4, false => 5 }));
            print(c && (1 < if d { 0 } else { 2 }));
        }";
    assert_eq!(out(src), "11\n8\n7\n3\n4\n56\n125\n90\n11\ntrue\n");
    verify(&lowered(src)).unwrap();
}

#[test]
fn short_circuit_and_side_effect_order_agree_across_engines() {
    let src = "
        fn t(n: i64) -> bool { print(n); true }
        fn f(n: i64) -> bool { print(n); false }
        fn main() {
            print(t(1) && f(2) && t(3));
            print(f(4) || t(5) || f(6));
            print(f(7) && t(8) || t(9));
            if t(10) && (f(11) || t(12)) { print(100); }
        }";
    assert_eq!(out(src), "1\n2\nfalse\n4\n5\ntrue\n7\n9\ntrue\n10\n11\n12\n100\n");
}

#[test]
fn match_lowering_nested_patterns_bindings_and_fallthrough() {
    let src = "
        enum E { A(i64, i64), B(bool), C }
        enum W { Wrap(E), Nil }
        fn f(w: W) -> i64 {
            match w {
                W::Wrap(E::A(0, y)) => 1000 + y,
                W::Wrap(E::A(x, y)) => x * 10 + y,
                W::Wrap(E::B(true)) => 7,
                W::Wrap(E::B(_)) => 8,
                W::Wrap(_) => 9,
                W::Nil => 0 - 1,
            }
        }
        fn main() {
            print(f(W::Wrap(E::A(0, 5)))); print(f(W::Wrap(E::A(3, 4)))); print(f(W::Wrap(E::B(true))));
            print(f(W::Wrap(E::B(false)))); print(f(W::Wrap(E::C))); print(f(W::Nil));
        }";
    assert_eq!(out(src), "1005\n34\n7\n8\n9\n-1\n");
}

#[test]
fn early_return_in_nested_control_flow_leaves_no_invalid_code() {
    let src = "
        fn find(a: [i64; 5], want: i64) -> i64 {
            let mut i = 0;
            while i < 5 { if a[i] == want { return i; } else { if a[i] > 100 { return 0 - 2; } } i = i + 1; }
            0 - 1
        }
        fn pick(b: bool) -> i64 { if b { return 1; } else { return 2; } }
        fn main() { let a = [5, 6, 7, 8, 9]; print(find(a, 7)); print(find(a, 1)); print(find([1, 200, 3, 4, 5], 3)); print(pick(true) + pick(false)); }";
    assert_eq!(out(src), "2\n-1\n-2\n3\n");
}

#[test]
fn runtime_errors_have_identical_messages_and_spans_in_both_engines() {
    for src in [
        "fn main() { let z = 0; print(1 / z); }",
        "fn main() { let a = [1, 2]; let i = 2; print(a[i]); }",
        "fn main() { let mut a = [1, 2]; let i = 7; a[i] = 3; }",
        "fn main() { let a: u8 = 255; print(a + 1); }",
        "fn main() { unsafe_free(); } fn unsafe_free() { let x: i8 = -128; print(-x); }",
        "fn f(n: i64) -> i64 { f(n + 1) } fn main() { print(f(0)); }",
        "@layer(hardware)\nfn main() { unsafe { poke(300, 1); } }",
        "fn main() { let x: u8 = 1; let n = 9; print(x << n); }",
    ] {
        match run2(src) {
            Err(RunError::Runtime(_)) => {}
            other => panic!("expected an identical runtime error from both engines for {:?}, got {:?}", src, other),
        }
    }
}

// ---------------------------------------------------------------- verifier negative tests

fn find_instr(p: &mut UProgram, pred: impl Fn(&UOp) -> bool) -> (usize, usize, usize) {
    for (fi, f) in p.fns.iter().enumerate() {
        for (bi, b) in f.blocks.iter().enumerate() {
            for (ii, ins) in b.instrs.iter().enumerate() { if pred(&ins.op) { return (fi, bi, ii); } }
        }
    }
    panic!("instruction not found");
}

fn expect_err(p: &UProgram, needle: &str) {
    match verify(p) {
        Ok(()) => panic!("verifier accepted bad UIR (wanted error containing {:?})", needle),
        Err(es) => assert!(es.iter().any(|e| e.contains(needle)), "no error containing {:?}: {:#?}", needle, es),
    }
}

#[test]
fn verifier_rejects_binary_type_mismatch() {
    let mut p = lowered("fn main() { let a = 1; let b = 2; print(a + b); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Binary(..)));
    let d = p.fns[f].blocks[b].instrs[i].dest.unwrap();
    p.fns[f].temps[d] = Ty::Bool;
    expect_err(&p, "bad binary operands");
}
#[test]
fn verifier_rejects_and_or_in_uir() {
    let mut p = lowered("fn main() { let a = 1; let b = 2; print(a + b); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Binary(..)));
    if let UOp::Binary(op, ..) = &mut p.fns[f].blocks[b].instrs[i].op { *op = BinOp::And; }
    expect_err(&p, "bad binary operands");
}
#[test]
fn verifier_rejects_store_into_slot_of_other_type() {
    let mut p = lowered("fn main() { let x = 1; print(x); }");
    p.fns[0].slots[0] = Ty::Bool;
    expect_err(&p, "store of");
}
#[test]
fn verifier_rejects_temp_used_outside_its_block() {
    let mut p = lowered("fn main() { let x = 1; if x == 1 { print(x); } }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Builtin(..)));
    assert!(b >= 1, "print should be in a later block");
    if let UOp::Builtin(_, args) = &mut p.fns[f].blocks[b].instrs[i].op { args[0] = 0; }
    expect_err(&p, "outside its defining block");
}
#[test]
fn verifier_rejects_use_before_definition() {
    let mut p = lowered("fn main() { let a = 1; let b = 2; print(a + b); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Binary(..)));
    let ins = p.fns[f].blocks[b].instrs.remove(i);
    p.fns[f].blocks[b].instrs.insert(0, ins);
    expect_err(&p, "used before definition");
}
#[test]
fn verifier_rejects_duplicate_definition() {
    let mut p = lowered("fn main() { let a = 1; let b = 2; print(a + b); }");
    let d0 = p.fns[0].blocks[0].instrs[0].dest.unwrap();
    p.fns[0].blocks[0].instrs[1].dest = Some(d0);
    expect_err(&p, "defined more than once");
}
#[test]
fn verifier_rejects_bad_branch_target() {
    let mut p = lowered("fn main() { let x = 1; if x == 1 { print(x); } }");
    for b in &mut p.fns[0].blocks { if let UTerm::CondBr(_, t, _) = &mut b.term { *t = 999; } }
    expect_err(&p, "out of range");
}
#[test]
fn verifier_rejects_non_bool_condition() {
    let mut p = lowered("fn main() { let x = 1; if x == 1 { print(x); } }");
    let c = match p.fns[0].blocks.iter().find_map(|b| if let UTerm::CondBr(c, ..) = b.term { Some(c) } else { None }) { Some(c) => c, None => panic!() };
    p.fns[0].temps[c] = Ty::Int(IntTy::I64);
    expect_err(&p, "condbr condition has type");
}
#[test]
fn verifier_rejects_return_type_mismatch() {
    let mut p = lowered("fn f() -> i64 { 1 } fn main() { print(f()); }");
    p.fns[0].ret = Ty::Bool;
    expect_err(&p, "ret type");
}
#[test]
fn verifier_rejects_call_arity_and_argument_types() {
    let mut p = lowered("fn f(a: i64, b: i64) -> i64 { a + b } fn main() { print(f(1, 2)); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Call(..)));
    if let UOp::Call(_, args) = &mut p.fns[f].blocks[b].instrs[i].op { args.pop(); }
    expect_err(&p, "passes 1 args, expects 2");
    let mut p = lowered("fn f(a: i64, b: i64) -> i64 { a + b } fn main() { print(f(1, 2)); }");
    p.fns[0].slots[1] = Ty::Bool;
    expect_err(&p, "argument 2");
}
#[test]
fn verifier_rejects_unresolved_types() {
    let mut p = lowered("fn main() { let x = 1; print(x); }");
    p.fns[0].temps[0] = Ty::Var(3);
    expect_err(&p, "unresolved/error type");
}
#[test]
fn verifier_rejects_incomplete_struct_literal_and_bad_fields() {
    let src = "struct S { a: i64, b: i64 } fn main() { let s = S { a: 1, b: 2 }; print(s.a); }";
    let mut p = lowered(src);
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::MakeStruct(..)));
    if let UOp::MakeStruct(_, fs) = &mut p.fns[f].blocks[b].instrs[i].op { fs.pop(); }
    expect_err(&p, "initialises 1 of 2 fields");
    let mut p = lowered(src);
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::LoadProj(..)));
    if let UOp::LoadProj(_, ps) = &mut p.fns[f].blocks[b].instrs[i].op { ps[0] = UProj::Field(9); }
    expect_err(&p, "field index out of range");
}
#[test]
fn verifier_rejects_out_of_range_slots_blocks_and_constants() {
    let mut p = lowered("fn main() { let x = 1; print(x); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Load(..)));
    p.fns[f].blocks[b].instrs[i].op = UOp::Load(999);
    expect_err(&p, "slot $999 out of range");
    let mut p = lowered("fn main() { let x: i8 = 5; print(x); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Const(_)));
    p.fns[f].blocks[b].instrs[i].op = UOp::Const(kendrah::hir::Value::Int(200));
    expect_err(&p, "does not fit");
    let mut p = lowered("fn main() {}");
    p.fns[0].blocks.clear();
    expect_err(&p, "no blocks");
}
#[test]
fn verifier_rejects_wrong_array_and_variant_typing() {
    let mut p = lowered("fn main() { let a = [1, 2, 3]; print(a[0]); }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::MakeArray(..)));
    let d = p.fns[f].blocks[b].instrs[i].dest.unwrap();
    p.fns[f].temps[d] = Ty::Array(Box::new(Ty::Int(IntTy::I64)), 5);
    expect_err(&p, "array literal has 3 elements");
    let mut p = lowered("enum E { A(i64), B } fn main() { let e = E::A(1); match e { E::A(n) => print(n), E::B => print(0) } }");
    let (f, b, i) = find_instr(&mut p, |o| matches!(o, UOp::Payload(..)));
    if let UOp::Payload(_, _, j) = &mut p.fns[f].blocks[b].instrs[i].op { *j = 4; }
    expect_err(&p, "payload index out of range");
}

// ---------------------------------------------------------------- fuel / step limits

#[test]
fn step_limit_stops_runaway_programs_on_both_engines() {
    let src = "fn main() { while true { } }";
    for engine in [Engine::Hir, Engine::Uir] {
        match run_source_with(src, engine, Some(10_000)) {
            Err(RunError::Runtime(e)) => assert!(e.message.contains("step limit"), "{:?}: {}", engine, e.message),
            other => panic!("{:?}: {:?}", engine, other),
        }
    }
    // a terminating program is unaffected by a generous limit
    assert_eq!(run_source_with("fn main() { print(1 + 1); }", Engine::Uir, Some(1_000)).unwrap(), "2\n");
}

#[test]
fn diverging_let_binding_is_rejected() {
    assert!(compile("fn f() -> i64 { let x = return 1; 2 } fn main() {}").is_err());
}

// ---------------------------------------------------------------- differential fuzzing of the two engines

struct Lcg(u64);
impl Lcg { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 17 } }

#[test]
fn engines_agree_on_mutants_of_every_example() {
    let mut rng = Lcg(31337);
    let (mut compared, mut skipped) = (0, 0);
    for (name, src) in examples() {
        let chars: Vec<char> = src.chars().collect();
        for _ in 0..700 {
            let mut c = chars.clone();
            let i = (rng.next() as usize) % c.len();
            let pool: Vec<char> = "0123456789+-*/%<>&|^=!".chars().collect();
            if c[i].is_ascii_digit() || "+-*/%<>&|^".contains(c[i]) { c[i] = pool[(rng.next() as usize) % pool.len()]; } else { continue; }
            let s: String = c.into_iter().collect();
            if compile(&s).is_err() { continue; }
            let s2 = s.clone();
            let r = std::thread::Builder::new().stack_size(256 << 20).spawn(move || {
                let fuel = Some(2_000_000);
                (run_source_with(&s2, Engine::Hir, fuel), run_source_with(&s2, Engine::Uir, fuel))
            }).unwrap().join().unwrap();
            let step_limited = |r: &Result<String, RunError>| matches!(r, Err(RunError::Runtime(e)) if e.message.contains("step limit"));
            if step_limited(&r.0) || step_limited(&r.1) { skipped += 1; continue; }
            match r {
                (Ok(a), Ok(b)) => assert_eq!(a, b, "{}: output differs for mutant:\n{}", name, s),
                (Err(RunError::Runtime(a)), Err(RunError::Runtime(b))) => assert_eq!(a, b, "{}: error differs for mutant:\n{}", name, s),
                (a, b) => panic!("{}: engines disagree ({:?} vs {:?}) for mutant:\n{}", name, a, b, s),
            }
            compared += 1;
        }
    }
    assert!(compared > 100, "too few compared mutants: {} (skipped {})", compared, skipped);
}

#[test]
fn len_of_a_local_array_is_a_constant_and_does_not_copy() {
    let u = lowered("fn main() { let a = [0; 100000]; let mut k = 0; while k < len(a) { k = k + 1; } print(k); }");
    assert!(!u.dump().contains("builtin len"), "{}", u.dump());
    // len of a non-place expression still evaluates its operand
    let u = lowered("fn mk() -> [i64; 3] { print(1); [1, 2, 3] } fn main() { print(len(mk())); }");
    assert!(u.dump().contains("builtin len"));
    assert_eq!(out("fn mk() -> [i64; 3] { print(1); [1, 2, 3] } fn main() { print(len(mk())); }"), "1\n3\n");
}
