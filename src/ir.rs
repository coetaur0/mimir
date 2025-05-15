//! Intermediate representation (IR) definition.

use std::collections::HashMap;

use crate::{source::Spanned, typing};

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
    pub origins: Vec<String>,
    pub locals: Vec<Local>,
    pub param_count: usize,
    pub body: Spanned<Block>,
}

impl Function {
    /// Get the type of a function.
    pub fn ty(&self) -> typing::Type {
        let params: Vec<typing::Type> = self.param_tys().iter().map(|ty| (*ty).into()).collect();
        let result = self.result_ty().into();
        typing::Type::Fn(params, Box::new(result))
    }

    /// Get the type annotations on a function's parameters.
    pub fn param_tys(&self) -> Vec<&Spanned<Type>> {
        self.locals[1..self.param_count + 1]
            .iter()
            .map(|p| &p.ty)
            .collect()
    }

    /// Get the return type annotation of a function.
    pub fn result_ty(&self) -> &Spanned<Type> {
        &self.locals[0].ty
    }
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
