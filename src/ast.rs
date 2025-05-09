//! Abstract syntax tree (AST) definition.

use std::collections::HashMap;

use crate::source::Spanned;

/// A module.
#[derive(Debug)]
pub struct Module {
    pub functions: HashMap<String, Function>,
}

/// A function declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub origins: Vec<Spanned<String>>,
    pub params: Vec<Local>,
    pub result: Spanned<Type>,
    pub body: Spanned<Block>,
}

/// A function parameter or local variable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Local {
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
    Let {
        variable: Local,
        value: Option<Spanned<Expr>>,
    },
    Assign {
        target: Spanned<Expr>,
        value: Spanned<Expr>,
    },
    Return(Spanned<Expr>),
    Expr(Expr),
}

/// An expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    If {
        cond: Box<Spanned<Self>>,
        then: Box<Spanned<Block>>,
        els: Box<Spanned<Self>>,
    },
    Call {
        callee: Box<Spanned<Self>>,
        args: Vec<Spanned<Self>>,
    },
    Borrow {
        mutable: bool,
        expr: Box<Spanned<Self>>,
    },
    Field {
        expr: Box<Spanned<Self>>,
        index: Spanned<usize>,
    },
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
    Fn {
        params: Vec<Spanned<Self>>,
        result: Box<Spanned<Self>>,
    },
    Ref {
        origin: Option<Spanned<String>>,
        mutable: bool,
        ty: Box<Spanned<Self>>,
    },
    Tuple(Vec<Spanned<Self>>),
    I32,
    Bool,
}
