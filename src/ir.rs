//! Intermediate representation (IR) definition.

use std::{collections::HashMap, fmt};

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
    pub origins: Vec<String>,
    pub locals: Vec<Local>,
    pub param_count: usize,
    pub body: Block,
}

impl Function {
    /// Get the function's type.
    pub fn ty(&self) -> Spanned<Type> {
        let params: Vec<Spanned<Type>> = self.locals[1..self.param_count + 1]
            .iter()
            .map(|p| p.ty.clone())
            .collect();
        let result = self.locals[0].ty.clone();
        let span = if let Some(ty) = params.first() {
            ty.span.start
        } else {
            result.span.start
        }..result.span.end;
        Spanned::new(Type::Fn(params, Box::new(result)), span)
    }
}

/// A function parameter or local variable declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Local {
    pub mutable: bool,
    pub ty: Spanned<Type>,
}

/// A block of instructions.
pub type Block = Vec<Instruction>;

/// An IR instruction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Instruction {
    If(Spanned<Operand>, Block, Block),
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

impl Spanned<Type> {
    /// Check if a type is equivalent to another.
    pub fn equiv_to(&self, other: &Spanned<Type>) -> bool {
        match (&self.item, &other.item) {
            (Type::Fn(l_params, l_result), Type::Fn(r_params, r_result)) => {
                l_params.len() == r_params.len()
                    && l_params.iter().zip(r_params).all(|(l, r)| l.equiv_to(r))
                    && l_result.equiv_to(r_result)
            }
            (Type::Ref(l_origin, l_mut, l_ty), Type::Ref(r_origin, r_mut, r_ty)) => {
                l_origin == r_origin && l_mut == r_mut && l_ty.equiv_to(r_ty)
            }
            (Type::Tuple(l_elems), Type::Tuple(r_elems)) => {
                l_elems.len() == r_elems.len()
                    && l_elems.iter().zip(r_elems).all(|(l, r)| l.equiv_to(r))
            }
            (Type::I32, Type::I32) | (Type::Bool, Type::Bool) => true,
            _ => false,
        }
    }

    /// Check if a type is a subtype of another.
    pub fn subtype_of(&self, other: &Spanned<Type>) -> bool {
        match (&self.item, &other.item) {
            (Type::Fn(l_params, l_result), Type::Fn(r_params, r_result)) => {
                l_params.len() == r_params.len()
                    && l_params.iter().zip(r_params).all(|(l, r)| r.subtype_of(l))
                    && l_result.subtype_of(r_result)
            }
            (Type::Ref(l_origin, l_mut, l_ty), Type::Ref(r_origin, r_mut, r_ty)) => {
                (r_origin.is_some_and(|rid| l_origin.is_some_and(|lid| lid == rid))
                    || r_origin.is_none())
                    && (*r_mut || !*l_mut)
                    && l_ty.subtype_of(r_ty)
            }
            (Type::Tuple(l_elems), Type::Tuple(r_elems)) => {
                l_elems.len() == r_elems.len()
                    && l_elems.iter().zip(r_elems).all(|(l, r)| l.subtype_of(r))
            }
            (l_ty, r_ty) => l_ty == r_ty,
        }
    }
}

impl fmt::Display for Spanned<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.item {
            Type::Fn(params, result) => {
                let params: Vec<String> = params.iter().map(|p| p.to_string()).collect();
                write!(f, "({}) -> {}", params.join(", "), result)
            }
            Type::Ref(origin, mutable, ty) => {
                if let Some(id) = origin {
                    write!(f, "&'{} {} {}", id, *mutable, ty)
                } else {
                    write!(f, "&{} {}", *mutable, ty)
                }
            }
            Type::Tuple(elems) => {
                let elems: Vec<String> = elems.iter().map(|p| p.to_string()).collect();
                write!(f, "({})", elems.join(", "))
            }
            Type::I32 => write!(f, "i32"),
            Type::Bool => write!(f, "bool"),
        }
    }
}
