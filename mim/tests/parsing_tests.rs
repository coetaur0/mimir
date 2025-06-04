use mim::parsing::*;
use mimir::reporting::{Error, Spanned};

#[test]
fn functions() {
    check_ok("fn f<'a>(r: &'a mut i32) -> i32 { *r } fn main() { f<'_>(&42) }");
    check_err(
        "fn f() {} fn f() {}",
        vec![Error::DuplicateFunction(Spanned::new(
            "f".to_string(),
            13..14,
        ))],
    );
    check_err(
        "fn f(x i32, y: 3) {}",
        vec![
            Error::UnexpectedToken(
                "a ':'".to_string(),
                Spanned::new(Token::I32Kw.to_string(), 7..10),
            ),
            Error::UnexpectedToken(
                "a type expression".to_string(),
                Spanned::new(Token::IntLit.to_string(), 15..16),
            ),
        ],
    );
    check_err(
        "fn f() -> {}",
        vec![Error::UnexpectedToken(
            "a type expression".to_string(),
            Spanned::new(Token::LBrace.to_string(), 10..11),
        )],
    );
}

#[test]
fn statements() {
    check_ok("fn main() { let x: i32 = 42; let b: bool; b = true; let c = 1; g(); return b }");
    check_ok("fn loop() { let mut cond = true; while cond { cond = false; } }");
    check_err(
        "fn main() { let x i32; }",
        vec![Error::UnclosedDelimiter(
            Spanned {
                item: "{".to_string(),
                span: 10..11,
            },
            Token::RBrace.to_string(),
            Spanned {
                item: Token::I32Kw.to_string(),
                span: 18..21,
            },
        )],
    );
    check_err(
        "fn main() { let x: 43; }",
        vec![Error::UnexpectedToken(
            "a type expression".to_string(),
            Spanned::new(Token::IntLit.to_string(), 19..21),
        )],
    );
    check_err(
        "fn main() { x = }",
        vec![Error::UnexpectedToken(
            "an expression".to_string(),
            Spanned::new(Token::RBrace.to_string(), 16..17),
        )],
    );
    check_err(
        "fn main() { return }",
        vec![Error::UnexpectedToken(
            "an expression".to_string(),
            Spanned::new(Token::RBrace.to_string(), 19..20),
        )],
    );
}

#[test]
fn expressions() {
    check_ok("fn main() { if b() { *r } else if c { &mut v } else { (0, false).0 } }");
    check_err(
        "fn main() { if true 32 else false }",
        vec![Error::UnexpectedToken(
            "a '{'".to_string(),
            Spanned::new(Token::IntLit.to_string(), 20..22),
        )],
    );
    check_err(
        "fn main() { f(x, y }",
        vec![Error::UnclosedDelimiter(
            Spanned::new("(".to_string(), 13..14),
            Token::RParen.to_string(),
            Spanned::new(Token::RBrace.to_string(), 19..20),
        )],
    );
    check_err(
        "fn main() { &i32 }",
        vec![Error::UnexpectedToken(
            "an expression".to_string(),
            Spanned::new(Token::I32Kw.to_string(), 13..16),
        )],
    );
    check_err(
        "fn main() { t.true }",
        vec![Error::UnexpectedToken(
            "an integer literal".to_string(),
            Spanned::new(Token::TrueLit.to_string(), 14..18),
        )],
    );
}

#[test]
fn types() {
    check_ok("fn f<'a, 'b>(x: &'a i32, f: fn(i32, i32) -> (bool, bool)) -> bool { }");
    check_err(
        "fn f(x: 3) {}",
        vec![Error::UnexpectedToken(
            "a type expression".to_string(),
            Spanned::new(Token::IntLit.to_string(), 8..9),
        )],
    );
    check_err(
        "fn f(x: fn( -> bool) {}",
        vec![Error::UnexpectedToken(
            "a type expression".to_string(),
            Spanned {
                item: Token::Arrow.to_string(),
                span: 12..14,
            },
        )],
    );
    check_err(
        "fn f() -> (i32 {}",
        vec![Error::UnclosedDelimiter(
            Spanned::new("(".to_string(), 10..11),
            Token::RParen.to_string(),
            Spanned::new(Token::LBrace.to_string(), 15..16),
        )],
    );
}

/// Check that parsing the declarations in a source string succeeds.
fn check_ok(src: &str) {
    assert!(parse(src).is_ok())
}

/// Check that parsing a source string returns the expected list of errors.
fn check_err(src: &str, expected: Vec<Error>) {
    match parse(src) {
        Ok(_) => panic!("Expected syntax errors in the input source."),
        Err(errors) => assert_eq!(errors, expected),
    }
}
