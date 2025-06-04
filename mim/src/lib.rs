use std::{fs, process};

use mimir::{analysis, reporting::Error, typing};

pub mod ast;
pub mod lowering;
pub mod parsing;

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
                    typing::check(&ir).unwrap_or_else(|errors| print_errors(&errors, path, &src));
                    for (name, function) in ir.functions {
                        println!("{}: {:#?}", name, function);
                        let sets = analysis::live(&function.body);
                        for set in sets.iter().rev() {
                            println!("    {:?}", set);
                        }
                    }
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
