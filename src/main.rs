use mim::{lowering::lower, parsing, source::Diagnostic, typing::check};

fn main() {
    let src = "fn f<'a>(a: &'a i32, b: &'a i32, c: bool) -> &'a i32 { if g(c) { a } else { h } } fn g(c: bool) -> bool { if c {false} else {true}}";
    match parsing::parse(src) {
        Ok(ast) => match lower(&ast) {
            Ok(ir) => match check(&ir) {
                Ok(_) => println!("{:#?}", ir),
                Err(errors) => {
                    for error in errors {
                        error.print("input", src);
                    }
                }
            },
            Err(errors) => {
                for error in errors {
                    error.print("input", src);
                }
            }
        },
        Err(errors) => {
            for error in errors {
                error.print("input", src);
            }
        }
    }
}
