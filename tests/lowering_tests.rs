use mim::{
    ir::Type,
    lowering::lower,
    parsing::parse,
    reporting::{Error, Spanned},
};

#[test]
fn functions() {
    check_ok("fn f<'a>(r: &'a mut i32) -> i32 { *r } fn main() { f<'_>(&42) }");
    check_ok(
        "fn f<'a, 'b>(x: &'a i32, f: fn(&'a i32, &'a i32) -> &'a i32) -> &'a i32 { f<'a>(x) }",
    );
    check_err(
        "fn f<'a, 'a>() {}",
        vec![Error::DuplicateOrigin(Spanned::new(
            "'a".to_string(),
            9..11,
        ))],
    );
    check_err(
        "fn f(x: i32, x: i32) {}",
        vec![Error::DuplicateParameter(Spanned::new(
            "x".to_string(),
            13..14,
        ))],
    );
}

#[test]
fn statements() {
    check_ok("fn f() -> i32 { let x: i32; x = 42; g(); return x; x } fn g() {}");
    check_err(
        "fn main() { let x; }",
        vec![Error::UndefinedType(Spanned::new("x".to_string(), 16..17))],
    );
    check_err(
        "fn main() { 3 = 4; }",
        vec![Error::UnassignableExpr(12..13)],
    );
}

#[test]
fn expressions() {
    check_ok(
        "fn main() { let x = 42; let r = &x; if g() { *r } else { (0, 1).1 }; } fn g() -> bool { true }",
    );
    check_err(
        "fn main() { 3(); }",
        vec![Error::InvalidCallee(Spanned::new(Type::I32, 12..13))],
    );
    check_err(
        "fn main() { 4.0 }",
        vec![Error::InvalidField(
            Spanned::new(Type::I32, 12..13),
            Spanned::new(0, 14..15),
        )],
    );
    check_err(
        "fn main() { *true; }",
        vec![Error::InvalidDeref(Spanned::new(Type::Bool, 13..17))],
    );
    check_err(
        "fn main() { x; }",
        vec![Error::UndefinedName(Spanned::new("x".to_string(), 12..13))],
    );
    check_err(
        "fn f<'a>() {} fn main() { f<'b>; }",
        vec![Error::UndefinedOrigin(28..30)],
    );
}

#[test]
fn types() {
    check_ok("fn f<'a, 'b>(x: &'a mut i32, f: fn(&'b i32) -> i32, t: (bool, i32)) -> i32 { true }");
    check_err("fn f(x: &'a i32) {}", vec![Error::UndefinedOrigin(9..11)]);
}

/// Check that lowering the declarations in a source string succeeds.
fn check_ok(src: &str) {
    assert!(parse(src).map(|ast| lower(&ast)).is_ok());
}

/// Check that lowering a source string returns the expected list of errors.
fn check_err(src: &str, expected: Vec<Error>) {
    match parse(src) {
        Ok(ast) => match lower(&ast) {
            Ok(_) => panic!("Expected lowering errors in the input source."),
            Err(errors) => assert_eq!(errors, expected),
        },
        Err(_) => panic!("Unexpected syntax errors in the input source."),
    }
}
