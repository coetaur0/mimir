//! Error reporting module.

use std::{ops::Range, result};

use ariadne::{Color, Label, Report, ReportKind, Source};

use crate::ir::Type;

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

/// A compiler result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A compilation error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    DuplicateFunction(Spanned<String>),
    DuplicateOrigin(Spanned<String>),
    DuplicateParameter(Spanned<String>),
    IncompatibleTypes(Type, Spanned<Type>),
    InvalidArg(Type, Spanned<Type>),
    InvalidArgNum(usize, Spanned<usize>),
    InvalidCallee(Spanned<Type>),
    InvalidCondition(Spanned<Type>),
    InvalidDeref(Spanned<Type>),
    InvalidField(Spanned<Type>, Spanned<usize>),
    InvalidOriginArgNum(Spanned<String>, usize, usize),
    OriginNeeded(Span),
    UnassignableExpr(Span),
    UnauthorizedBorrow(Span),
    UnclosedDelimiter(Spanned<String>, String, Spanned<String>),
    UndefinedGlobal(Spanned<String>),
    UndefinedLocal(Span),
    UndefinedName(Spanned<String>),
    UndefinedOrigin(Span),
    UndefinedType(Spanned<String>),
    UnexpectedToken(String, Spanned<String>),
}

impl Error {
    /// Print the error given some source `path` and `contents`.
    pub fn print(&self, path: &str, contents: &str) {
        match self {
            Error::DuplicateFunction(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(1)
                    .with_message("Duplicate function declaration.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "A function named {} has already been defined in the module.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::DuplicateOrigin(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(2)
                    .with_message("Duplicate origin declaration.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "An origin named {} has already been defined in the module.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::DuplicateParameter(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(3)
                    .with_message("Duplicate parameter declaration.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "A parameter named {} has already been defined in the module.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::IncompatibleTypes(expected, found) => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(4)
                    .with_message("Incompatible types.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "Expected a value of type {}, but found type {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidArg(expected, found) => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(5)
                    .with_message("Invalid argument type.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "Expected a value of type {}, but found type {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidArgNum(expected, found) => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(6)
                    .with_message("Invalid number of arguments.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "Expected {} arguments for the call, but found {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidCallee(callee) => {
                Report::build(ReportKind::Error, (path, callee.span.clone()))
                    .with_code(7)
                    .with_message("Invalid call.")
                    .with_label(
                        Label::new((path, callee.span.clone()))
                            .with_message(format!("Cannot call a value of type {}.", callee.item))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidCondition(cond) => {
                Report::build(ReportKind::Error, (path, cond.span.clone()))
                    .with_code(8)
                    .with_message("Invalid condition.")
                    .with_label(
                        Label::new((path, cond.span.clone()))
                            .with_message(format!(
                                "Expected a value of type bool, but found {}.",
                                cond.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidDeref(value) => {
                Report::build(ReportKind::Error, (path, value.span.clone()))
                    .with_code(9)
                    .with_message("Invalid dereference.")
                    .with_label(
                        Label::new((path, value.span.clone()))
                            .with_message(format!(
                                "Cannot dereference a value of type {}.",
                                value.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidField(value, index) => {
                Report::build(ReportKind::Error, (path, value.span.start..index.span.end))
                    .with_code(10)
                    .with_message("Invalid field.")
                    .with_label(
                        Label::new((path, index.span.clone()))
                            .with_message(format!(
                                "Cannot access field {} in a value of type {}.",
                                index.item, value.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidOriginArgNum(name, expected, found) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(11)
                    .with_message("Invalid number of origin arguments.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "Expected {} origin arguments for the function {}, but found {}.",
                                expected, name.item, found
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::OriginNeeded(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(12)
                .with_message("Missing an origin specifier.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message(
                            "All references in function parameters and return types must be annotated with origins.",
                        )
                        .with_color(Color::Red),
                ),
            Error::UnassignableExpr(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(13)
                .with_message("Non-assignable expression.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message(
                            "Cannot assign a value to an expression that is not a field, a dereference or a variable.",
                        )
                        .with_color(Color::Red),
                ),
            Error::UnauthorizedBorrow(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(14)
                .with_message("Unatuthorized borrow.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message(
                            "Cannot borrow this expression as mutable.",
                        )
                        .with_color(Color::Red),
                ),
            Error::UnclosedDelimiter(open, expected, found) => {
                Report::build(ReportKind::Error, (path, open.span.clone()))
                    .with_code(15)
                    .with_message("Unclosed delimiter.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "Expected a {}, but found {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::UndefinedGlobal(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(16)
                    .with_message("Undefined function.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "No function named {} was found in the module.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::UndefinedLocal(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(17)
                .with_message("Undefined variable.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message(
                            "No variable with this name in scope.",
                        )
                        .with_color(Color::Red),
                ),
            Error::UndefinedName(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(18)
                    .with_message("Undefined variable.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "No variable named {} was found in the scope.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::UndefinedOrigin(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(19)
                .with_message("Undefined origin.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message(
                            "No origin with this name in scope.",
                        )
                        .with_color(Color::Red),
                ),
            Error::UndefinedType(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(20)
                    .with_message("Unknown type.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "Cannot determine the type of {}. Please annotate the definition with a type.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::UnexpectedToken(expected, found) => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(21)
                    .with_message("Unexpected symbol.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "Expected {}, but found {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
        }
        .finish()
        .eprint((path, Source::from(contents)))
        .unwrap()
    }
}
