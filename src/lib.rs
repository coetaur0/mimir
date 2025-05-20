use std::{fs, process};

use source::Diagnostic;

pub mod ast;
pub mod ir;
pub mod lowering;
pub mod naming;
pub mod parsing;
pub mod source;
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
                    typing::check(&ir)
                        .unwrap_or_else(|errors| print_diagnostics(&errors, path, &src))
                })
                .unwrap_or_else(|errors| print_diagnostics(&errors, path, &src))
        })
        .unwrap_or_else(|errors| print_diagnostics(&errors, path, &src));
}

/// Print a list of diagnostics to stderr.
fn print_diagnostics<D: Diagnostic>(diags: &[D], path: &str, src: &str) {
    for diag in diags {
        diag.print(path, src);
    }
}
