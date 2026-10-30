//! M4.3: owned heap `String`, move checking, drop elaboration (docs/MEMORY.md section 3).
//! Every positive program runs on the HIR interpreter, the UIR interpreter and native code. The interpreters report
//! a leaked or doubly freed String as an internal error, and the native runtime exits 70 on a leak, so a passing
//! run also proves that every allocation was freed exactly once.
use kendrah::{run_differential, RunError};

fn ok(src: &str) -> String {
    let a = match run_differential(src, None) { Ok(o) => o, Err(e) => panic!("{:?}\n{}", e, src) };
    let b = match kendrah::native::run_native_differential(src, 1) { Ok(o) => o, Err(e) => panic!("native: {:?}\n{}", e, src) };
    assert_eq!(a, b, "engines differ for\n{}", src);
    a
}

fn rejects(src: &str, needle: &str) {
    match kendrah::compile(src) {
        Err(ds) => {
            let m = ds.iter().map(|d| format!("{}:{}: {}", d.span.line, d.span.col, d.message)).collect::<Vec<_>>().join("\n");
            assert!(m.contains(needle), "expected `{}` in:\n{}\nfor\n{}", needle, m, src);
        }
        Ok(_) => panic!("expected a compile error containing `{}` for\n{}", needle, src),
    }
}

fn accepts(src: &str) { if let Err(e) = kendrah::compile(src) { panic!("{:?}\n{}", e, src) } }

#[test]
fn basic_operations() {
    assert_eq!(ok("fn main() { let s = string_from(\"hi\"); print(&s); print(string_len(&s)); }"), "hi\n2\n");
    assert_eq!(ok("fn main() { let a = string_from(\"foo\"); let b = string_from(\"bar\"); let c = string_concat(&a, &b); print(&c); print(string_len(&c)); print(&a); }"), "foobar\n6\nfoo\n");
    assert_eq!(ok("fn main() { let mut s = string_from(\"a\"); string_push(&mut s, \"bc\"); string_push(&mut s, \"\"); string_push(&mut s, \"def\"); print(&s); }"), "abcdef\n");
    assert_eq!(ok("fn main() { let s = string_from(\"héllo\"); print(string_len(&s)); let t = string_clone(&s); print(string_eq(&s, &t)); let u = string_from(\"x\"); print(string_eq(&s, &u)); }"), "6\ntrue\nfalse\n");
    assert_eq!(ok("fn main() { let e = string_from(\"\"); print(string_len(&e)); print(&e); }"), "0\n\n");
}

#[test]
fn ownership_transfer_and_drops() {
    assert_eq!(ok("fn eat(s: String) -> i64 { string_len(&s) } fn main() { let s = string_from(\"four\"); print(eat(s)); }"), "4\n");
    assert_eq!(ok("fn mk() -> String { string_from(\"made\") } fn twice(s: &String) -> String { string_concat(s, s) } fn main() { let a = mk(); let b = twice(&a); print(&b); print(&a); }"), "mademade\nmade\n");
    assert_eq!(ok("fn add(s: &mut String) { string_push(s, \"!\"); } fn main() { let mut s = string_from(\"hey\"); add(&mut s); add(&mut s); print(&s); }"), "hey!!\n");
    assert_eq!(ok("fn pass(s: String) -> String { s } fn main() { let s = pass(pass(string_from(\"id\"))); print(&s); }"), "id\n");
    assert_eq!(ok("fn main() { let s = { let a = string_from(\"in\"); a }; print(&s); }"), "in\n");
    // discarded temporaries and overwritten values are freed
    assert_eq!(ok("fn main() { string_from(\"gone\"); string_clone(&string_from(\"x\")); print(1); }".replace("string_clone(&string_from(\"x\"));", "").as_str()), "1\n");
    assert_eq!(ok("fn main() { let mut s = string_from(\"a\"); s = string_concat(&s, &s); s = string_concat(&s, &s); print(&s); s = string_from(\"z\"); print(&s); }"), "aaaa\nz\n");
    assert_eq!(ok("fn eat(s: String) {} fn main() { let mut s = string_from(\"a\"); eat(s); s = string_from(\"again\"); print(&s); }"), "again\n");
    assert_eq!(ok("fn set(r: &mut String) { *r = string_from(\"replaced\"); } fn main() { let mut s = string_from(\"old\"); set(&mut s); print(&s); }"), "replaced\n");
}

#[test]
fn control_flow_drops_on_every_path() {
    assert_eq!(ok("fn f(c: bool) -> i64 { let a = string_from(\"a\"); if c { let b = string_from(\"bb\"); return string_len(&b); } let d = string_from(\"ddd\"); string_len(&a) + string_len(&d) } fn main() { print(f(true)); print(f(false)); }"), "2\n4\n");
    assert_eq!(ok("fn main() { let mut s = string_from(\"\"); let mut i = 0; while i < 5 { string_push(&mut s, \"ab\"); i = i + 1; } print(string_len(&s)); }"), "10\n");
    assert_eq!(ok("fn main() { let mut i = 0; let mut n = 0; while i < 2000 { let t = string_from(\"x\"); n = n + string_len(&t); i = i + 1; } print(n); }"), "2000\n");
    assert_eq!(ok("fn eat(s: String) -> i64 { 1 } fn main() { let s = string_from(\"x\"); let c = true; let r = if c { eat(s) } else { 0 }; print(r); }"), "1\n");
    assert_eq!(ok("fn f(i: i64) -> i64 { let s = string_from(\"loop\"); let mut k = 0; while k < 10 { let t = string_clone(&s); if k == i { return string_len(&t) + k; } k = k + 1; } 0 } fn main() { print(f(3)); print(f(99)); }"), "7\n0\n");
    assert_eq!(ok("fn build(n: i64) -> String { if n == 0 { string_from(\"\") } else { let mut s = build(n - 1); string_push(&mut s, \"x\"); s } } fn main() { print(string_len(&build(0 + 50))); }".replace("&build(0 + 50)", "&b").replace("print(string_len(&b))", "let b = build(50); print(string_len(&b))").as_str()), "50\n");
    assert_eq!(ok("fn pick(c: bool, a: String, b: String) -> String { if c { a } else { b } } fn main() { let r = pick(false, string_from(\"A\"), string_from(\"B\")); print(&r); }"), "B\n");
    assert_eq!(ok("fn main() { let mut s = string_from(\"\"); let mut i = 0; while i < 100000 { string_push(&mut s, \"ab\"); i = i + 1; } print(string_len(&s)); }"), "200000\n");
}

#[test]
fn runtime_error_with_live_strings_is_still_reported_normally() {
    let r = run_differential("fn main() { let s = string_from(\"a\"); let z = 0; print(1 / z); }", None);
    match r { Err(RunError::Runtime(e)) => assert_eq!(e.message, "division by zero"), o => panic!("{:?}", o) }
    let n = kendrah::native::run_native("fn main() { let s = string_from(\"a\"); let z = 0; print(1 / z); }", "t.kd", 1).unwrap();
    assert_eq!(n.code, 2);
    assert!(n.stderr.contains("division by zero"));
}

#[test]
fn use_after_move_is_rejected() {
    let eat = "fn eat(s: String) {} ";
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); eat(a); eat(a); }}"), "use of moved value `a`");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); let b = a; print(&a); }}"), "borrow of moved value `a`");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); let b = a; let c = a; }}"), "use of moved value `a`");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); let mut i = 0; while i < 3 {{ eat(a); i = i + 1; }} }}"), "use of moved value `a`");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); if true {{ eat(a); }} print(string_len(&a)); }}"), "borrow of moved value `a`");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); if true {{ eat(a); }} else {{ }} eat(a); }}"), "use of moved value `a`");
    rejects(&format!("{eat} fn f(s: String) {{ eat(s); eat(s); }} fn main() {{}}"), "use of moved value `s`");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); let r = &a; eat(a); print(string_len(r)); }}"), "cannot move out of `a` because it is borrowed");
    rejects(&format!("{eat} fn main() {{ let a = string_from(\"x\"); eat(a); let r = &a; }}"), "borrow of moved value `a`");
}

#[test]
fn moves_that_are_fine_are_accepted() {
    let eat = "fn eat(s: String) {} ";
    accepts(&format!("{eat} fn main() {{ let mut a = string_from(\"x\"); eat(a); a = string_from(\"y\"); eat(a); }}"));
    accepts(&format!("{eat} fn main() {{ let a = string_from(\"x\"); if true {{ eat(a); return; }} eat(a); }}"));
    accepts(&format!("{eat} fn main() {{ let a = string_from(\"x\"); let b = string_clone(&a); eat(a); eat(b); }}"));
    accepts(&format!("{eat} fn main() {{ let mut i = 0; while i < 3 {{ let a = string_from(\"x\"); eat(a); i = i + 1; }} }}"));
}

#[test]
fn owned_values_cannot_hide_in_aggregates_or_be_copied() {
    accepts("struct S { s: String } fn main() {}");
        rejects("fn main() { let a = [string_from(\"x\")]; }", "cannot be stored in arrays");
    rejects("fn f(a: [String; 2]) {} fn main() {}", "cannot be stored in arrays");
    rejects("fn main() { let s = string_from(\"x\"); let r = &s; let t = *r; }", "cannot move an owned `String` out of a reference");
    rejects("fn main() { let s = string_from(\"x\"); match s { _ => {} } }", "cannot `match` on an owned `String`");
    rejects("fn main() { let s = string_from(\"x\"); print(s); }", "cannot print a value of type String");
    rejects("fn main() { let a = string_from(\"x\"); let b = string_from(\"y\"); let c = a + b; }", "operator `+` cannot be applied");
    rejects("fn main() { let s = string_from(\"x\"); string_push(&s, \"y\"); }", "mismatched types in argument 1 of `string_push`");
    rejects("fn main() { let s = string_from(\"x\"); string_push(&mut s, \"y\"); }", "cannot borrow `s` as mutable");
    rejects("fn main() { let s = string_from(5); }", "mismatched types in argument 1 of `string_from`");
    rejects("fn main() { let s: i64 = string_from(\"x\"); }", "mismatched types");
    rejects("@layer(declarative) fn f() -> i64 { let s = string_from(\"x\"); 1 }", "heap allocation");
    accepts("fn f(s: &String) -> String { string_clone(s) } fn main() { let s = string_from(\"x\"); let t = f(&s); }");
}
