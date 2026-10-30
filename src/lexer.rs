//! Lexer: source text -> tokens. Tracks 1-based line/column.

use crate::diag::{Diag, Span};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Int(u64),
    Float(f64),
    Str(String),
    Ident(String),
    Fn, Let, Mut, If, Else, While, Return, True, False, Unsafe, As, Struct, Enum, Match, Mod, Pub, For, In, DotDot, Use, Break, Continue, Impl,
    At, LParen, RParen, LBrace, RBrace, LBracket, RBracket, Comma, Colon, ColonColon, Semi, Arrow, FatArrow, Dot,
    Amp, Pipe, Caret, Shl, Shr,
    Plus, Minus, Star, Slash, Percent,
    Assign, EqEq, Ne, Lt, Le, Gt, Ge, AndAnd, OrOr, Bang,
    Eof,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

pub fn lex(src: &str) -> Result<Vec<Token>, Diag> {
    let cs: Vec<char> = src.chars().collect();
    let (mut i, mut line, mut col) = (0usize, 1u32, 1u32);
    let mut out = Vec::new();

    macro_rules! adv {
        () => {{
            if cs[i] == '\n' { line += 1; col = 1; } else { col += 1; }
            i += 1;
        }};
    }

    while i < cs.len() {
        let c = cs[i];
        let span = Span { line, col };
        if c.is_whitespace() { adv!(); continue; }
        if c == '/' && i + 1 < cs.len() && cs[i + 1] == '/' {
            while i < cs.len() && cs[i] != '\n' { adv!(); }
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            while i < cs.len() && cs[i].is_ascii_digit() { adv!(); }
            let mut is_float = false;
            if i + 1 < cs.len() && cs[i] == '.' && cs[i + 1].is_ascii_digit() {
                is_float = true;
                adv!();
                while i < cs.len() && cs[i].is_ascii_digit() { adv!(); }
            }
            let text: String = cs[start..i].iter().collect();
            let tok = if is_float {
                Tok::Float(text.parse().map_err(|_| Diag::new(span, "invalid float literal"))?)
            } else {
                Tok::Int(text.parse().map_err(|_| Diag::new(span, format!("integer literal `{}` does not fit in u64", text)))?)
            };
            out.push(Token { tok, span });
            continue;
        }
        if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < cs.len() && (cs[i].is_alphanumeric() || cs[i] == '_') { adv!(); }
            let text: String = cs[start..i].iter().collect();
            let tok = match text.as_str() {
                "fn" => Tok::Fn, "let" => Tok::Let, "mut" => Tok::Mut, "if" => Tok::If,
                "else" => Tok::Else, "while" => Tok::While, "for" => Tok::For, "use" => Tok::Use, "impl" => Tok::Impl, "break" => Tok::Break, "continue" => Tok::Continue, "in" => Tok::In, "return" => Tok::Return,
                "true" => Tok::True, "false" => Tok::False, "unsafe" => Tok::Unsafe, "as" => Tok::As,
                "struct" => Tok::Struct, "enum" => Tok::Enum, "match" => Tok::Match, "mod" => Tok::Mod, "pub" => Tok::Pub,
                _ => Tok::Ident(text),
            };
            out.push(Token { tok, span });
            continue;
        }
        if c == '"' {
            adv!();
            let mut s = String::new();
            loop {
                if i >= cs.len() { return Err(Diag::new(span, "unterminated string literal")); }
                let ch = cs[i];
                if ch == '"' { adv!(); break; }
                if ch == '\n' { return Err(Diag::new(span, "unterminated string literal")); }
                if ch == '\\' {
                    adv!();
                    if i >= cs.len() { return Err(Diag::new(span, "unterminated string literal")); }
                    let e = cs[i];
                    s.push(match e {
                        'n' => '\n', 't' => '\t', '"' => '"', '\\' => '\\',
                        other => return Err(Diag::new(Span { line, col }, format!("unknown escape `\\{}`", other))),
                    });
                    adv!();
                } else {
                    s.push(ch);
                    adv!();
                }
            }
            out.push(Token { tok: Tok::Str(s), span });
            continue;
        }
        let next = cs.get(i + 1).copied();
        let (tok, len) = match (c, next) {
            ('-', Some('>')) => (Tok::Arrow, 2),
            ('=', Some('>')) => (Tok::FatArrow, 2),
            (':', Some(':')) => (Tok::ColonColon, 2),
            ('<', Some('<')) => (Tok::Shl, 2),
            ('>', Some('>')) => (Tok::Shr, 2),
            ('=', Some('=')) => (Tok::EqEq, 2),
            ('!', Some('=')) => (Tok::Ne, 2),
            ('<', Some('=')) => (Tok::Le, 2),
            ('>', Some('=')) => (Tok::Ge, 2),
            ('&', Some('&')) => (Tok::AndAnd, 2),
            ('|', Some('|')) => (Tok::OrOr, 2),
            ('.', Some('.')) => (Tok::DotDot, 2),
            ('@', _) => (Tok::At, 1), ('(', _) => (Tok::LParen, 1), (')', _) => (Tok::RParen, 1),
            ('[', _) => (Tok::LBracket, 1), (']', _) => (Tok::RBracket, 1), ('.', _) => (Tok::Dot, 1),
            ('&', _) => (Tok::Amp, 1), ('|', _) => (Tok::Pipe, 1), ('^', _) => (Tok::Caret, 1),
            ('{', _) => (Tok::LBrace, 1), ('}', _) => (Tok::RBrace, 1), (',', _) => (Tok::Comma, 1),
            (':', _) => (Tok::Colon, 1), (';', _) => (Tok::Semi, 1), ('+', _) => (Tok::Plus, 1),
            ('-', _) => (Tok::Minus, 1), ('*', _) => (Tok::Star, 1), ('/', _) => (Tok::Slash, 1),
            ('%', _) => (Tok::Percent, 1), ('=', _) => (Tok::Assign, 1), ('<', _) => (Tok::Lt, 1),
            ('>', _) => (Tok::Gt, 1), ('!', _) => (Tok::Bang, 1),
            _ => return Err(Diag::new(span, format!("unexpected character `{}`", c))),
        };
        for _ in 0..len { adv!(); }
        out.push(Token { tok, span });
    }
    out.push(Token { tok: Tok::Eof, span: Span { line, col } });
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Tok> { lex(s).unwrap().into_iter().map(|t| t.tok).collect() }

    #[test]
    fn basic_tokens() {
        assert_eq!(toks("let x = 1 + 2.5;"), vec![
            Tok::Let, Tok::Ident("x".into()), Tok::Assign, Tok::Int(1), Tok::Plus, Tok::Float(2.5), Tok::Semi, Tok::Eof]);
    }
    #[test]
    fn two_char_ops_and_arrow() {
        assert_eq!(toks("-> == != <= >= && ||"), vec![Tok::Arrow, Tok::EqEq, Tok::Ne, Tok::Le, Tok::Ge, Tok::AndAnd, Tok::OrOr, Tok::Eof]);
    }
    #[test]
    fn comments_and_strings() {
        assert_eq!(toks("// hi\n\"a\\nb\""), vec![Tok::Str("a\nb".into()), Tok::Eof]);
    }
    #[test]
    fn positions() {
        let t = lex("fn\n  main").unwrap();
        assert_eq!(t[1].span, Span { line: 2, col: 3 });
    }
    #[test]
    fn errors() {
        assert!(lex("\"abc").is_err());
        assert!(lex("#").is_err());
        assert!(lex("99999999999999999999").is_err());
        assert!(lex("\"\\q\"").is_err());
    }
    #[test]
    fn int_dot_without_digit_is_not_float() {
        // `1.` is not a float literal. Since M1 `.` is a token (field access), so it lexes as Int, Dot;
        // the parser rejects it (see tests/m1.rs::float_literal_requires_digits_after_dot).
        assert_eq!(toks("1."), vec![Tok::Int(1), Tok::Dot, Tok::Eof]);
    }
    #[test]
    fn m1_tokens() {
        assert_eq!(toks("a::b => [x] . & | ^ << >>"), vec![Tok::Ident("a".into()), Tok::ColonColon, Tok::Ident("b".into()), Tok::FatArrow,
            Tok::LBracket, Tok::Ident("x".into()), Tok::RBracket, Tok::Dot, Tok::Amp, Tok::Pipe, Tok::Caret, Tok::Shl, Tok::Shr, Tok::Eof]);
    }
    #[test]
    fn u64_max_literal_lexes() {
        assert_eq!(toks("18446744073709551615"), vec![Tok::Int(u64::MAX), Tok::Eof]);
        assert!(lex("18446744073709551616").is_err());
    }
}
