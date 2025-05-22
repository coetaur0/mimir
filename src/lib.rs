use std::{fs, process};

use crate::reporting::Error;

pub mod ast;
pub mod ir;
pub mod lowering;
pub mod parsing;
pub mod reporting;
pub mod typing;

/// Compile the module in a file at some `path`.
pub fn compile(path: &str) {
    let src = fs::read_to_string(path).unwrap_or_else(|err| {
        println!("Error: {err}.");
        process::exit(2)
    });

    parsing::parse(&src)
        .map(|ast| {
            lowering::lower(&ast)
                .map(|ir| {
                    typing::check(&ir).unwrap_or_else(|errors| print_errors(&errors, path, &src))
                })
                .unwrap_or_else(|errors| print_errors(&errors, path, &src))
        })
        .unwrap_or_else(|errors| print_errors(&errors, path, &src));
}

/// Print a list of errors to stderr.
fn print_errors(errors: &[Error], path: &str, src: &str) {
    for error in errors {
        error.print(path, src);
    }
}
