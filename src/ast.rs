//! Abstract syntax tree (AST) definition.

use std::collections::HashMap;

use crate::Spanned;

/// A module.
#[derive(Debug)]
pub struct Module {
    pub functions: HashMap<String, Function>,
}

/// A function declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub origins: Vec<Spanned<String>>,
    pub params: Vec<Parameter>,
    pub result: Spanned<Type>,
    pub body: Block,
}

impl Function {
    /// Get the function's AST type.
    pub fn ty(&self) -> Spanned<Type> {
        let span = if self.params.is_empty() {
            self.result.span.start
        } else {
            self.params[0].ty.span.start
        }..self.result.span.end;
        Spanned::new(
            Type::Fn(
                self.params.iter().map(|p| p.ty.clone()).collect(),
                Box::new(self.result.clone()),
            ),
            span,
        )
    }
}

/// A function parameter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Parameter {
    pub mutable: bool,
    pub name: Spanned<String>,
    pub ty: Spanned<Type>,
}

/// A block expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub stmts: Vec<Spanned<Stmt>>,
    pub result: Spanned<Expr>,
}

/// A statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Stmt {
    Let(
        bool,
        Spanned<String>,
        Option<Spanned<Type>>,
        Option<Spanned<Expr>>,
    ),
    Assign(Spanned<Expr>, Spanned<Expr>),
    Return(Spanned<Expr>),
    Expr(Expr),
}

/// An expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    If(Box<Spanned<Self>>, Box<Spanned<Block>>, Box<Spanned<Self>>),
    Call(Box<Spanned<Self>>, Vec<Spanned<Self>>),
    Borrow(bool, Box<Spanned<Self>>),
    Field(Box<Spanned<Self>>, Spanned<usize>),
    Deref(Box<Spanned<Self>>),
    Tuple(Vec<Spanned<Self>>),
    Block(Box<Block>),
    Name(String),
    Int(i32),
    Bool(bool),
}

/// A type expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Fn(Vec<Spanned<Self>>, Box<Spanned<Self>>),
    Ref(Option<Spanned<String>>, bool, Box<Spanned<Self>>),
    Tuple(Vec<Spanned<Self>>),
    I32,
    Bool,
}
