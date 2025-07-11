//! Intermediate representation (IR) definition.

use std::{collections::HashMap, fmt};

use crate::reporting::Spanned;

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
    pub origin_count: usize,
    pub param_count: usize,
    pub locals: Vec<Local>,
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
pub type Block = Vec<Statement>;

/// An IR statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    While(Spanned<Operand>, Block),
    If(Spanned<Operand>, Block, Block),
    Call(Spanned<Place>, Spanned<Operand>, Vec<Spanned<Operand>>),
    Borrow(Spanned<Place>, bool, Spanned<Place>),
    Assign(Spanned<Place>, Spanned<Operand>),
    Return,
}

/// An instruction operand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Operand {
    Place(Place),
    Fn(Spanned<String>, Vec<Option<OriginId>>),
    Int(i32),
    Bool(bool),
    Unit,
}

/// A place expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Place {
    Deref(Box<Spanned<Self>>),
    Local(LocalId),
}

/// A type expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Fn(Vec<Spanned<Self>>, Box<Spanned<Self>>),
    Ref(Option<OriginId>, bool, Box<Spanned<Self>>),
    I32,
    Bool,
    Unit,
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
            (Type::I32, Type::I32) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => true,
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
                    && (*l_mut || !*r_mut)
                    && l_ty.subtype_of(r_ty)
            }
            (_, _) => self.equiv_to(other),
        }
    }

    /// Substitute the origin ids in a type.
    pub fn substitute(&self, subst: &[Option<OriginId>]) -> Spanned<Type> {
        match &self.item {
            Type::Fn(params, result) => Spanned::new(
                Type::Fn(
                    params.iter().map(|p| p.substitute(subst)).collect(),
                    Box::new(result.substitute(subst)),
                ),
                self.span.clone(),
            ),
            Type::Ref(origin, mutability, ref_ty) => {
                let new_origin = origin
                    .map(|id| {
                        if id < subst.len() {
                            subst[id]
                        } else {
                            Some(id)
                        }
                    })
                    .unwrap_or(None);
                Spanned::new(
                    Type::Ref(new_origin, *mutability, Box::new(ref_ty.substitute(subst))),
                    self.span.clone(),
                )
            }
            Type::I32 | Type::Bool | Type::Unit => self.clone(),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Type::Fn(params, result) => {
                let params: Vec<String> = params.iter().map(|p| p.item.to_string()).collect();
                write!(f, "({}) -> {}", params.join(", "), result.item)
            }
            Type::Ref(origin, mutable, ty) => {
                let mutability = if *mutable { "mut " } else { "" };
                if let Some(id) = origin {
                    write!(f, "&'{} {}{}", id, mutability, ty.item)
                } else {
                    write!(f, "&{}{}", mutability, ty.item)
                }
            }
            Type::I32 => write!(f, "i32"),
            Type::Bool => write!(f, "bool"),
            Type::Unit => write!(f, "()"),
        }
    }
}
