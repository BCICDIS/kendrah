//! M1.5 (part 3): `break` / `continue` (HIR interp, UIR interp, native; owned values are dropped on early exits).
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
        Ok(_) => panic!("expected error {}", needle),
    }
}

#[test]
fn break_and_continue_in_while_and_for() {
    assert_eq!(ok("fn main() { let mut i = 0; while true { if i == 3 { break; } print(i); i = i + 1; } print(99); }"), "0\n1\n2\n99\n");
    assert_eq!(ok("fn main() { let mut i = 0; while i < 6 { i = i + 1; if i % 2 == 0 { continue; } print(i); } }"), "1\n3\n5\n");
    assert_eq!(ok("fn main() { for i in 0..10 { if i == 2 { continue; } if i == 5 { break; } print(i); } }"), "0\n1\n3\n4\n");
    assert_eq!(ok("fn main() { for i in 0..3 { for j in 0..3 { if j == 1 { continue; } if j == 2 { break; } print(i * 10 + j); } } }"), "0\n10\n20\n");
    assert_eq!(ok("fn first(a: [i64; 5], x: i64) -> i64 { let mut r = 0 - 1; for i in 0..5 { if a[i] == x { r = i; break; } } r } fn main() { print(first([4, 5, 6, 5, 4], 5)); print(first([1, 1, 1, 1, 1], 9)); }"), "1\n-1\n");
    assert_eq!(ok("fn main() { let mut n = 0; while n < 3 { n = n + 1; break } print(n); }"), "1\n");
    assert_eq!(ok("fn f() -> i64 { let mut i = 0; while true { i = i + 1; if i > 4 { return i; } continue; } 0 } fn main() { print(f()); }"), "5\n");
}

#[test]
fn early_exits_drop_owned_values() {
    assert_eq!(ok("fn main() { let mut i = 0; while i < 5 { let s = string_from(\"abc\"); i = i + 1; if i == 2 { continue; } if i == 4 { break; } print(string_len(&s) + i); } print(i); }"), "4\n6\n4\n".replace("4\n6\n4\n", "4\n6\n4\n").as_str().replace("6\n4\n", "6\n4\n").as_str());
    assert_eq!(ok("fn main() { for i in 0..4 { let a = string_from(\"x\"); { let b = string_clone(&a); if i == 1 { continue; } if i == 3 { break; } print(string_len(&b)); } } }"), "1\n1\n");
    assert_eq!(ok("fn eat(s: String) {} fn main() { for i in 0..3 { let a = string_from(\"x\"); if i == 1 { eat(a); continue; } print(i); } }"), "0\n2\n");
    assert_eq!(ok("fn main() { let keep = string_from(\"k\"); for i in 0..3 { let t = string_clone(&keep); if i == 1 { break; } } print(&keep); }"), "k\n");
}

#[test]
fn misuse_is_rejected() {
    rejects("fn main() { break; }", "`break` outside of a loop");
    rejects("fn main() { continue; }", "`continue` outside of a loop");
    rejects("fn f() { if true { break; } } fn main() {}", "outside of a loop");
    rejects("fn eat(s: String) {} fn main() { let a = string_from(\"x\"); while true { eat(a); break; } eat(a); }", "moved value `a`");
    rejects("fn eat(s: String) {} fn main() { let a = string_from(\"x\"); for i in 0..3 { if i == 1 { eat(a); continue; } } }", "moved value `a`");
    rejects("fn eat(s: String) {} fn main() { let a = string_from(\"x\"); for i in 0..3 { if i == 1 { eat(a); break; } } print(string_len(&a)); }", "moved value `a`");
    assert!(kendrah::compile("fn eat(s: String) {} fn main() { let a = string_from(\"x\"); while true { eat(a); break; } }").is_ok());
}
