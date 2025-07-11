use mimir::{
    ir::Type,
    lowering::lower,
    parsing::parse,
    reporting::{Error, Spanned},
    typing::check,
};

#[test]
fn functions() {
    check_ok("fn f<'a>(r: &'a mut i32) -> i32 { *r } fn main() { f<'_>(&42) }");
    check_ok(
        "fn f<'a, 'b>(x: &'a i32, f: fn(&'a i32, &'a i32) -> &'a i32) -> &'a i32 { f<'a>(x) }",
    );

    check_err("fn f(r: &i32) {}", vec![Error::OriginNeeded(9..12)]);
    check_err(
        "fn f() -> bool { 42 }",
        vec![Error::IncompatibleTypes(
            Type::Bool,
            Spanned::new(Type::I32, 17..19),
        )],
    );
}

#[test]
fn statements() {
    check_ok("fn f() -> i32 { let x: i32; x = 42; g(); return x; x } fn g() {}");
    check_ok("fn loop() { let mut cond = true; while cond { cond = false; } }");

    check_err(
        "fn f() -> i32 { return false }",
        vec![
            Error::IncompatibleTypes(Type::I32, Spanned::new(Type::Bool, 23..28)),
            Error::IncompatibleTypes(
                Type::I32,
                Spanned {
                    item: Type::Unit,
                    span: 30..30,
                },
            ),
        ],
    );
    check_err(
        "fn main() { while 0 {} }",
        vec![Error::InvalidCondition(Spanned::new(Type::I32, 18..19))],
    );
}

#[test]
fn expressions() {
    check_ok(
        "fn main() { let x = 42; let r = &x; if g() { *r } else { 1 }; } fn g() -> bool { true }",
    );

    check_err(
        "fn main() { if 0 { 1 } else { 2 }; }",
        vec![Error::InvalidCondition(Spanned::new(Type::I32, 15..16))],
    );
    check_err(
        "fn f<'a, 'b>() {} fn main() { let f = f<'_>; }",
        vec![Error::InvalidOriginArgNum(
            Spanned::new("f".to_string(), 38..39),
            2,
            1,
        )],
    );
    check_err(
        "fn f(x: i32, y: i32) {} fn main() { f(3) }",
        vec![Error::InvalidArgNum(2, Spanned::new(1, 36..37))],
    );
    check_err(
        "fn f(x: i32, y: i32) {} fn main() { f(true, false) }",
        vec![
            Error::InvalidArg(Type::I32, Spanned::new(Type::Bool, 38..42)),
            Error::InvalidArg(Type::I32, Spanned::new(Type::Bool, 44..49)),
        ],
    );
    check_err(
        "fn f<'a, 'b>(x: &'a i32, g: fn(&'b i32) -> ()) { g<'b>(x) }",
        vec![Error::InvalidArg(
            Type::Ref(Some(1), false, Box::new(Spanned::new(Type::I32, 35..38))),
            Spanned::new(
                Type::Ref(Some(0), false, Box::new(Spanned::new(Type::I32, 20..23))),
                55..56,
            ),
        )],
    );
    check_err(
        "fn main() { let x = 42; let y = &mut x; }",
        vec![Error::UnauthorizedBorrow(37..38)],
    );
}

#[test]
fn types() {
    check_ok("fn f<'a, 'b>(x: &'a mut i32, f: fn(&'b i32) -> (), t: bool) -> i32 { true }");
}

/// Check that type checking the declarations in a source string succeeds.
fn check_ok(src: &str) {
    assert!(
        parse(src)
            .map(|ast| lower(&ast).map(|ir| check(&ir)))
            .is_ok()
    );
}

/// Check that type checking a source string returns the expected list of errors.
fn check_err(src: &str, expected: Vec<Error>) {
    match parse(src) {
        Ok(ast) => match lower(&ast) {
            Ok(ir) => match check(&ir) {
                Ok(_) => panic!("Expected type errors in the input source."),
                Err(errors) => assert_eq!(errors, expected),
            },
            Err(_) => panic!("Unexpected lowering errors in the input source."),
        },
        Err(_) => panic!("Unexpected syntax errors in the input source."),
    }
}
