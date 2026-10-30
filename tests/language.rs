use kendrah::{compile, run_differential, RunError};

/// Run on a large stack (the tree-walker recurses natively).
fn run(src: &str) -> Result<String, RunError> {
    let s = src.to_string();
    std::thread::Builder::new().stack_size(256 * 1024 * 1024)
        .spawn(move || run_differential(&s, None)).unwrap().join().unwrap()
}
fn out(src: &str) -> String { run(src).unwrap_or_else(|e| panic!("expected success, got {:?}", e)) }
fn main_body(body: &str) -> String { format!("fn main() {{ {} }}", body) }

fn compile_errors(src: &str) -> Vec<String> {
    match compile(src) {
        Ok(_) => panic!("expected compile error for:\n{}", src),
        Err(ds) => ds.into_iter().map(|d| format!("{}:{}: {}", d.span.line, d.span.col, d.message)).collect(),
    }
}
fn rejects(src: &str, needle: &str) {
    let errs = compile_errors(src);
    assert!(errs.iter().any(|e| e.contains(needle)), "no error containing {:?}; got {:#?}", needle, errs);
}
fn runtime_error(src: &str) -> String {
    match run(src) { Err(RunError::Runtime(e)) => e.message, other => panic!("expected runtime error, got {:?}", other) }
}

// ---------- parsing / evaluation ----------

#[test]
fn precedence_and_associativity() {
    assert_eq!(out(&main_body("print(2 + 3 * 4); print(10 - 4 - 3); print((2 + 3) * 4); print(100 / 10 / 5); print(-2 * 3);")), "14\n3\n20\n2\n-6\n");
}
#[test]
fn comparison_and_logic() {
    assert_eq!(out(&main_body("print(1 < 2 && 2 < 3); print(1 > 2 || false); print(!true); print(3 == 3); print(\"a\" != \"b\");")), "true\nfalse\nfalse\ntrue\ntrue\n");
}
#[test]
fn short_circuit() {
    // right side would divide by zero if evaluated
    assert_eq!(out(&main_body("let z = 0; print(false && 1 / z == 0); print(true || 1 / z == 0);")), "false\ntrue\n");
}
#[test]
fn strings_and_floats() {
    assert_eq!(out(&main_body("print(\"ab\" + \"cd\"); print(1.5 + 2.25); print(7.0 / 2.0); print(3.0);")), "abcd\n3.75\n3.5\n3.0\n");
}
#[test]
fn casts() {
    assert_eq!(out(&main_body("print(7 as f64 / 2.0); print(3.99 as i64); print(-3.99 as i64); print(true as i64);")), "3.5\n3\n-3\n1\n");
}
#[test]
fn if_is_an_expression_and_else_if_chains() {
    let src = "fn sign(x: i64) -> i64 { if x < 0 { -1 } else if x == 0 { 0 } else { 1 } }
               fn main() { print(sign(-5)); print(sign(0)); print(sign(9)); }";
    assert_eq!(out(src), "-1\n0\n1\n");
}
#[test]
fn block_expressions_and_shadowing_and_scopes() {
    assert_eq!(out(&main_body("let x = 1; let y = { let x = 10; x + 1 }; print(x); print(y); let x = x + 100; print(x);")), "1\n11\n101\n");
}
#[test]
fn assignment_in_inner_scope_updates_outer() {
    assert_eq!(out(&main_body("let mut a = 0; { a = 5; } if true { a = a + 1; } print(a);")), "6\n");
}
#[test]
fn mutual_recursion_and_forward_references() {
    let src = "fn main() { print(is_even(10)); print(is_even(7)); }
               fn is_even(n: i64) -> bool { if n == 0 { true } else { is_odd(n - 1) } }
               fn is_odd(n: i64) -> bool { if n == 0 { false } else { is_even(n - 1) } }";
    assert_eq!(out(src), "true\nfalse\n");
}
#[test]
fn early_return_inside_loop() {
    let src = "fn first_over(limit: i64) -> i64 { let mut i = 0; while true { if i * i > limit { return i; } i = i + 1; } 0 }
               fn main() { print(first_over(50)); }";
    assert_eq!(out(src), "8\n");
}
#[test]
fn comments_are_ignored() {
    assert_eq!(out("// c1\nfn main() { // c2\n print(1); // c3\n }"), "1\n");
}

// ---------- compile-time rejection ----------

#[test] fn rejects_type_mismatch_in_binary_op() { rejects(&main_body("print(1 + 2.0);"), "cannot be applied to i64 and f64"); }
#[test] fn rejects_undefined_variable() { rejects(&main_body("print(x);"), "undefined variable `x`"); }
#[test] fn rejects_undefined_function() { rejects(&main_body("foo();"), "undefined function `foo`"); }
#[test] fn rejects_wrong_arg_count() { rejects("fn f(a: i64) {} fn main() { f(1, 2); }", "takes 1 argument(s) but 2"); }
#[test] fn rejects_wrong_arg_type() { rejects("fn f(a: i64) {} fn main() { f(true); }", "expected i64, found bool"); }
#[test] fn rejects_assignment_to_immutable() { rejects(&main_body("let x = 1; x = 2;"), "immutable variable `x`"); }
#[test] fn rejects_assignment_type_mismatch() { rejects(&main_body("let mut x = 1; x = \"s\";"), "`x` is i64 but assigned str"); }
#[test] fn rejects_wrong_declared_type() { rejects(&main_body("let x: bool = 1;"), "declared bool but initializer is i64"); }
#[test] fn rejects_non_bool_condition() { rejects(&main_body("if 1 { }"), "condition must be bool"); rejects(&main_body("while 1 { }"), "condition must be bool"); }
#[test] fn rejects_missing_return_value() { rejects("fn f() -> i64 { let x = 1; }", "must evaluate to i64"); }
#[test] fn rejects_return_type_mismatch() { rejects("fn f() -> i64 { return true; }", "returns i64 but this returns bool"); }
#[test] fn rejects_if_branch_mismatch() { rejects("fn f() -> i64 { if true { 1 } else { \"x\" } }", "different types"); }
#[test] fn rejects_if_without_else_with_value() { rejects("fn f() -> i64 { if true { 1 }; 2 }", "without `else`"); }
#[test] fn rejects_duplicate_function() { rejects("fn f() {} fn f() {} fn main() {}", "defined more than once"); }
#[test] fn rejects_builtin_redefinition() { rejects("fn print(x: i64) {} fn main() {}", "builtin"); }
#[test] fn rejects_bad_main_signature() { rejects("fn main(x: i64) {}", "`main` must take no parameters"); }
#[test] fn rejects_bad_cast() { rejects(&main_body("print(\"a\" as i64);"), "cannot cast str to i64"); }
#[test] fn rejects_scope_leak() { rejects(&main_body("{ let inner = 1; } print(inner);"), "undefined variable `inner`"); }
#[test] fn rejects_unit_binding() { rejects("fn f() {} fn main() { let x = f(); }", "type ()"); }
#[test] fn rejects_duplicate_param() { rejects("fn f(a: i64, a: i64) {} fn main() {}", "duplicate parameter"); }

#[test]
fn reports_multiple_errors_with_locations() {
    let errs = compile_errors("fn main() {\n  print(a);\n  print(b);\n}");
    assert_eq!(errs.len(), 2);
    assert!(errs[0].starts_with("2:9:"), "{:?}", errs);
    assert!(errs[1].starts_with("3:9:"), "{:?}", errs);
}
#[test]
fn error_cascade_is_suppressed() {
    // One undefined variable should yield one diagnostic, not a chain.
    assert_eq!(compile_errors(&main_body("let y = x + 1; print(y * 2);")).len(), 1);
}
#[test]
fn diagnostic_rendering_has_caret_under_column() {
    let src = "fn main() {\n  print(zz);\n}";
    let d = &compile(src).unwrap_err()[0];
    let r = d.render(src, "t.kd");
    assert!(r.starts_with("t.kd:2:9: error: undefined variable `zz`"), "{}", r);
    assert!(r.contains("  |         ^"), "{}", r);
}

// ---------- syntax errors ----------

#[test] fn syntax_missing_semicolon() { rejects("fn main() { print(1) print(2); }", "expected `;`"); }
#[test] fn syntax_missing_brace() { rejects("fn main() { print(1);", "missing `}`"); }
#[test] fn syntax_param_needs_type() { rejects("fn f(a) {}", "type annotation"); }
#[test] fn syntax_let_needs_init() { rejects("fn main() { let x; }", "must be initialized"); }
#[test] fn syntax_unknown_type() { rejects("fn f(a: float) {}", "unknown type `float`"); }
#[test] fn syntax_stray_token() { rejects("fn main() { ) }", "expected an expression"); }

// ---------- runtime semantics ----------

#[test] fn runtime_division_by_zero() { assert!(runtime_error(&main_body("let z = 0; print(1 / z);")).contains("division by zero")); }
#[test] fn runtime_remainder_by_zero() { assert!(runtime_error(&main_body("let z = 0; print(1 % z);")).contains("remainder by zero")); }
#[test] fn runtime_add_overflow() { assert!(runtime_error(&main_body("let m = 9223372036854775807; print(m + 1);")).contains("overflow")); }
#[test] fn runtime_mul_overflow() { assert!(runtime_error(&main_body("let m = 9223372036854775807; print(m * 2);")).contains("overflow")); }
#[test] fn runtime_neg_overflow() { assert!(runtime_error(&main_body("let m = 0 - 9223372036854775807 - 1; print(-m);")).contains("overflow")); }
#[test] fn runtime_min_div_neg1_overflow() { assert!(runtime_error(&main_body("let m = 0 - 9223372036854775807 - 1; print(m / -1);")).contains("overflow")); }
#[test] fn float_division_by_zero_is_ieee() { assert_eq!(out(&main_body("print(1.0 / 0.0);")), "inf\n"); }
#[test]
fn runtime_stack_overflow_is_an_error_not_a_crash() {
    let m = runtime_error("fn f(n: i64) -> i64 { f(n + 1) } fn main() { print(f(0)); }");
    assert!(m.contains("stack overflow"), "{}", m);
}
#[test]
fn deep_but_legal_recursion_works() {
    assert_eq!(out("fn sum(n: i64) -> i64 { if n == 0 { 0 } else { n + sum(n - 1) } } fn main() { print(sum(1500)); }"), "1125750\n");
}
#[test]
fn missing_main_is_reported() {
    match run("fn f() {}") { Err(RunError::Runtime(e)) => assert!(e.message.contains("main")), o => panic!("{:?}", o) }
}

// ---------- @layer semantics ----------

const HW: &str = "@layer(hardware)\n";

#[test]
fn unsafe_rejected_outside_hardware_layer() {
    rejects("fn main() { unsafe { poke(0, 1); } }", "only permitted in @layer(hardware)");
    rejects("@layer(declarative)\nfn f() -> i64 { unsafe { peek(0) } }", "only permitted in @layer(hardware)");
}
#[test]
fn peek_poke_require_unsafe_even_in_hardware() {
    rejects(&format!("{}fn main() {{ poke(0, 1); }}", HW), "requires an `unsafe` block");
    rejects(&format!("{}fn main() {{ print(peek(0)); }}", HW), "requires an `unsafe` block");
}
#[test]
fn hardware_unsafe_memory_roundtrip() {
    assert_eq!(out(&format!("{}fn main() {{ unsafe {{ poke(7, 200); poke(8, 1); print(peek(7) + peek(8)); }} }}", HW)), "201\n");
}
#[test]
fn unsafe_memory_is_bounds_checked() {
    let m = runtime_error(&format!("{}fn main() {{ unsafe {{ poke(256, 1); }} }}", HW));
    assert!(m.contains("out of bounds"), "{}", m);
    let m = runtime_error(&format!("{}fn main() {{ unsafe {{ print(peek(0 - 1)); }} }}", HW));
    assert!(m.contains("out of bounds"), "{}", m);
    let m = runtime_error(&format!("{}fn main() {{ unsafe {{ poke(0, 256); }} }}", HW));
    assert!(m.contains("does not fit in a byte"), "{}", m);
}
#[test]
fn memory_starts_zeroed() {
    assert_eq!(out(&format!("{}fn main() {{ unsafe {{ print(peek(0)); print(peek(255)); }} }}", HW)), "0\n0\n");
}
#[test]
fn declarative_forbids_mutation_loops_and_effects() {
    let d = "@layer(declarative)\n";
    rejects(&format!("{}fn f() -> i64 {{ let mut x = 1; x }}", d), "mutable binding is not permitted in @layer(declarative)");
    rejects(&format!("{}fn f() {{ while true {{ }} }}", d), "`while` loop is not permitted");
    rejects(&format!("{}fn f() -> i64 {{ print(1); 1 }}", d), "`print` has side effects");
}
#[test]
fn declarative_may_only_call_declarative() {
    rejects("@layer(declarative)\nfn f() -> i64 { g() }\n@layer(application)\nfn g() -> i64 { 1 }", "may only call declarative functions");
    rejects("@layer(declarative)\nfn f() -> i64 { g() }\n@layer(hardware)\nfn g() -> i64 { 1 }", "may only call declarative functions");
    assert_eq!(out("@layer(declarative)\nfn sq(x: i64) -> i64 { x * x }\n@layer(declarative)\nfn f() -> i64 { sq(3) + sq(4) }\nfn main() { print(f()); }"), "25\n");
}
#[test]
fn application_may_call_all_layers_and_hardware_wrappers_hide_unsafe() {
    let src = "@layer(hardware)\nfn put(a: i64, v: i64) { unsafe { poke(a, v); } }
               @layer(hardware)\nfn get(a: i64) -> i64 { unsafe { peek(a) } }
               @layer(declarative)\nfn dbl(x: i64) -> i64 { x * 2 }
               fn main() { put(3, dbl(21)); print(get(3)); }";
    assert_eq!(out(src), "42\n");
}
#[test]
fn module_level_layer_sets_default_and_function_attr_overrides() {
    // Module default is declarative, so `main` (declarative) cannot print...
    rejects("@layer(declarative);\nfn main() { print(1); }", "not permitted in @layer(declarative)");
    // ...unless it is overridden per function.
    assert_eq!(out("@layer(declarative);\n@layer(application)\nfn main() { print(1); }"), "1\n");
}
#[test]
fn layer_declaration_errors() {
    rejects("fn f() {}\n@layer(hardware);", "must appear before all functions");
    rejects("@layer(hardware);\n@layer(hardware);\nfn main() {}", "duplicate module-level @layer");
    rejects("@layer(quantum)\nfn main() {}", "unknown layer `quantum`");
    rejects("@inline\nfn main() {}", "unknown attribute");
}

// ---------- examples (expected output computed by hand, stored in .out files) ----------

#[test]
fn examples_produce_expected_output() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut n = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let p = entry.unwrap().path();
        if p.extension().and_then(|e| e.to_str()) != Some("kd") { continue; }
        let want = std::fs::read_to_string(p.with_extension("out")).unwrap_or_else(|_| panic!("missing .out for {:?}", p));
        let src = std::fs::read_to_string(&p).unwrap();
        assert_eq!(out(&src), want, "example {:?}", p);
        n += 1;
    }
    assert!(n >= 3, "expected at least 3 examples, found {}", n);
}

// ---------- differential test: generated integer expressions vs. Rust's own arithmetic ----------

struct Lcg(u64);
impl Lcg { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 } }

/// Returns (kendrah source, expected value or None if Rust detects overflow/div-by-zero).
fn gen(rng: &mut Lcg, depth: u32) -> (String, Option<i64>) {
    if depth == 0 || rng.next() % 4 == 0 {
        let v = (rng.next() % 2000) as i64 - 1000;
        // negative literals are written as parenthesised unary minus
        return if v < 0 { (format!("(-{})", -v), Some(v)) } else { (v.to_string(), Some(v)) };
    }
    let (ls, lv) = gen(rng, depth - 1);
    let (rs, rv) = gen(rng, depth - 1);
    let op = rng.next() % 5;
    let (sym, val) = match (lv, rv) {
        (Some(a), Some(b)) => match op {
            0 => ("+", a.checked_add(b)), 1 => ("-", a.checked_sub(b)), 2 => ("*", a.checked_mul(b)),
            3 => ("/", a.checked_div(b)), _ => ("%", a.checked_rem(b)),
        },
        _ => (["+", "-", "*", "/", "%"][op as usize], None),
    };
    (format!("({} {} {})", ls, sym, rs), val)
}

#[test]
fn differential_integer_expressions_match_rust() {
    let mut rng = Lcg(0xC0FFEE);
    let (mut ok, mut err) = (0, 0);
    for _ in 0..400 {
        let (src, expect) = gen(&mut rng, 5);
        let prog = main_body(&format!("print({});", src));
        match (expect, run(&prog)) {
            (Some(v), Ok(o)) => { assert_eq!(o, format!("{}\n", v), "expr {}", src); ok += 1; }
            (None, Err(RunError::Runtime(_))) => { err += 1; }
            (e, r) => panic!("mismatch for {}: expected {:?}, got {:?}", src, e, r),
        }
    }
    assert!(ok > 100 && err > 5, "weak coverage: ok={} err={}", ok, err);
}

// ---------- parser robustness: never panic on garbage ----------

#[test]
fn frontend_never_panics_on_mutated_input() {
    let base = std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/layers.kd")).unwrap();
    let chars: Vec<char> = base.chars().collect();
    let mut rng = Lcg(42);
    for _ in 0..1500 {
        let mut c = chars.clone();
        for _ in 0..(1 + rng.next() % 4) {
            let i = (rng.next() as usize) % c.len();
            match rng.next() % 3 {
                0 => { c.remove(i); }
                1 => { c[i] = "(){};,+-*/=<>!@\"x1 ".chars().nth((rng.next() % 19) as usize).unwrap(); }
                _ => { c.insert(i, "{}();@".chars().nth((rng.next() % 6) as usize).unwrap()); }
            }
            if c.is_empty() { break; }
        }
        let s: String = c.into_iter().collect();
        let _ = compile(&s); // must return Ok/Err, never panic
    }
}
