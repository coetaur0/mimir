use std::{fs, ops::Range, process};

pub mod ast;
pub mod ir;
pub mod lowering;
pub mod parsing;
pub mod typing;

/// A span between two offsets in a source.
pub type Span = Range<usize>;

/// An item associated with a span in a source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Spanned<T> {
    pub item: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    /// Create a new spanned item.
    pub fn new(item: T, span: Span) -> Self {
        Spanned { item, span }
    }
}

/// A compiler diagnostic reporting an issue in some source.
pub trait Diagnostic {
    /// Print the diagnostic, given some source `path` and `contents`.
    fn print(&self, path: &str, contents: &str);
}

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
