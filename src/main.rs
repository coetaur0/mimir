use mim::{lowering::lower, parsing, source::Diagnostic};

fn main() {
    let src = "fn f<'a>(a: &'a i32, b: &'a i32, c: bool) -> &'a i32 { if c { a } else { b } }";
    match parsing::parse(src) {
        Ok(ast) => match lower(&ast) {
            Ok(ir) => println!("{:#?}", ir),
            Err(errors) => {
                for error in errors {
                    println!("{:#?}", error);
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
