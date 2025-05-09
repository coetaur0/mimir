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
    If {
        cond: Spanned<Operand>,
        then: Spanned<Block>,
        els: Spanned<Block>,
    },
    Call {
        target: Spanned<Place>,
        callee: Spanned<Place>,
        args: Vec<Spanned<Operand>>,
    },
    Borrow {
        target: Spanned<Place>,
        mutable: bool,
        place: Spanned<Place>,
    },
    Value {
        target: Spanned<Place>,
        operand: Spanned<Operand>,
    },
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
    Field {
        place: Box<Spanned<Self>>,
        index: Spanned<usize>,
    },
    Deref(Box<Spanned<Self>>),
    Global(String),
    Local(LocalId),
}

/// A type expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Fn {
        params: Vec<Spanned<Self>>,
        result: Box<Spanned<Self>>,
    },
    Ref {
        origin: Option<OriginId>,
        mutable: bool,
        ty: Box<Spanned<Self>>,
    },
    Tuple(Vec<Spanned<Self>>),
    I32,
    Bool,
}
