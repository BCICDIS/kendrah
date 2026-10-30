//! M1.5 (part 1): `for i in a..b` (desugared to a checked counted `while`).
use kendrah::run_differential;

fn ok(src: &str) -> String {
    let a = run_differential(src, None).unwrap_or_else(|e| panic!("{:?}\n{}", e, src));
    let b = kendrah::native::run_native_differential(src, 1).unwrap_or_else(|e| panic!("native {:?}\n{}", e, src));
    assert_eq!(a, b);
    a
}

#[test]
fn counts_and_nests() {
    assert_eq!(ok("fn main() { for i in 0..3 { print(i); } }"), "0\n1\n2\n");
    assert_eq!(ok("fn main() { for i in 3..3 { print(i); } for i in 5..2 { print(i); } print(9); }"), "9\n");
    assert_eq!(ok("fn main() { let mut s = 0; for i in 0..4 { for j in 0..i { s = s + j; } } print(s); }"), "4\n");
    assert_eq!(ok("fn main() { let n: u8 = 4; for i in 250..255 { print(i); } for k in 0..n { print(k); } }"), "250\n251\n252\n253\n254\n0\n1\n2\n3\n");
    assert_eq!(ok("fn main() { let mut t = 0; for i in 1..=1 + 3 { t = t + i; } print(t); }".replace("1..=1 + 3", "1..1 + 4").as_str()), "10\n");
}

#[test]
fn return_shadowing_and_arrays() {
    assert_eq!(ok("fn find(a: [i64; 4], x: i64) -> i64 { for i in 0..4 { if a[i] == x { return i; } } 0 - 1 } fn main() { print(find([5, 6, 7, 8], 7)); print(find([5, 6, 7, 8], 1)); }"), "2\n-1\n");
    assert_eq!(ok("fn main() { let i = 100; for i in 0..2 { print(i); } print(i); }"), "0\n1\n100\n");
    assert_eq!(ok("fn main() { let mut a = [0; 5]; for i in 0..5 { a[i] = i * i; } let mut s = 0; for i in 0..5 { s = s + a[i]; } print(s); }"), "30\n");
}

#[test]
fn loop_var_is_a_fresh_immutable_binding_and_strings_work() {
    assert!(kendrah::compile("fn main() { for i in 0..3 { i = 5; } }").is_err());
    assert_eq!(ok("fn main() { let mut s = string_from(\"\"); for i in 0..3 { string_push(&mut s, \"ab\"); let t = string_clone(&s); print(string_len(&t)); } }"), "2\n4\n6\n");
    assert!(kendrah::compile("fn main() { for i in 0..3 }").is_err());
    assert!(kendrah::compile("fn main() { for i in 0 { } }").is_err());
    assert!(kendrah::compile("fn main() { for i in 0..3 { print(i) } }").is_ok());
}

#[test]
fn bounds_must_have_same_integer_type() {
    assert!(kendrah::compile("fn main() { let a: u8 = 1; let b: i64 = 5; for i in a..b { } }").is_err());
}
