//! Source related types and functions.

use std::ops::Range;

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
