//! Intermediate representation (IR) definition.

use std::collections::HashMap;

use crate::source::Spanned;

/// An origin identifier.
pub type OriginId = usize;

/// A local (function parameter or variable) identifier.
pub type LocalId = usize;

/// An IR module.
#[derive(Debug)]
pub struct Module {
    pub functions: HashMap<String, Function>,
}

/// A function declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub origins: Vec<Option<String>>,
    pub locals: Vec<Local>,
    pub param_count: usize,
    pub body: Spanned<Block>,
}

/// A function parameter or local variable declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Local {
    pub mutable: bool,
    pub name: Option<Spanned<String>>,
    pub ty: Spanned<Type>,
}

/// A block of instructions.
pub type Block = Vec<Spanned<Instruction>>;

/// An IR instruction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Instruction {
    If(Spanned<Operand>, Spanned<Block>, Spanned<Block>),
    Call(Spanned<Place>, Spanned<Place>, Vec<Spanned<Operand>>),
    Borrow(Spanned<Place>, bool, Spanned<Place>),
    Value(Spanned<Place>, Spanned<Operand>),
    Return,
}

/// An instruction operand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Operand {
    Tuple(Vec<Spanned<Self>>),
    Place(Place),
    Int(i32),
    Bool(bool),
}

/// A place expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Place {
    Field(Box<Spanned<Self>>, Spanned<usize>),
    Deref(Box<Spanned<Self>>),
    Global(String),
    Local(LocalId),
}

/// A type expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Fn(Vec<Spanned<Self>>, Box<Spanned<Self>>),
    Ref(Option<OriginId>, bool, Box<Spanned<Self>>),
    Tuple(Vec<Spanned<Self>>),
    I32,
    Bool,
}
