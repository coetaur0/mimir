//! Typing functions.

use std::result;

use crate::{
    ir::{self, Local, Module, OriginId, Place},
    source::{Span, Spanned},
};

/// A typing result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A typing error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    InvalidIndex {
        ty: Spanned<Type>,
        index: Spanned<usize>,
    },
    InvalidDeref(Spanned<Type>),
    UndefinedGlobal(Spanned<String>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Fn(Vec<Self>, Box<Self>),
    Ref(Option<OriginId>, bool, Box<Self>),
    Tuple(Vec<Self>),
    I32,
    Bool,
}

impl Type {
    /// Check if a type is a subtype of another.
    fn subtype_of(&self, other: &Self) -> bool {
        match (&self, &other) {
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

impl From<&Spanned<ir::Type>> for Type {
    fn from(value: &Spanned<ir::Type>) -> Self {
        match &value.item {
            ir::Type::Fn(params, result) => Type::Fn(
                params.iter().map(|p| p.into()).collect(),
                Box::new(result.as_ref().into()),
            ),
            ir::Type::Ref(origin, is_mut, ty) => {
                Type::Ref(*origin, *is_mut, Box::new(ty.as_ref().into()))
            }
            ir::Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| e.into()).collect()),
            ir::Type::I32 => Type::I32,
            ir::Type::Bool => Type::Bool,
        }
    }
}

/// Type check a place expression.
fn check_place(module: &Module, locals: &[Local], place: &Spanned<Place>) -> Result<(bool, Type)> {
    match &place.item {
        Place::Field(place, index) => check_index(module, locals, place, index),
        Place::Deref(place) => check_deref(module, locals, place),
        Place::Global(name) => check_global(module, name, &place.span),
        Place::Local(id) => Ok((locals[*id].mutable, (&locals[*id].ty).into())),
    }
}

/// Type check a place index expression.
fn check_index(
    module: &Module,
    locals: &[Local],
    place: &Spanned<Place>,
    index: &Spanned<usize>,
) -> Result<(bool, Type)> {
    let (is_mut, ty) = check_place(module, locals, place)?;
    match ty {
        Type::Tuple(elems) if index.item < elems.len() => Ok((is_mut, elems[index.item].clone())),
        _ => Err(vec![Error::InvalidIndex {
            ty: Spanned::new(ty, place.span.clone()),
            index: index.clone(),
        }]),
    }
}

/// Type check a place dereference expression.
fn check_deref(module: &Module, locals: &[Local], place: &Spanned<Place>) -> Result<(bool, Type)> {
    let (_, ty) = check_place(module, locals, place)?;
    match ty {
        Type::Ref(_, is_mut, ty) => Ok((is_mut, *ty)),
        _ => Err(vec![Error::InvalidDeref(Spanned::new(
            ty,
            place.span.clone(),
        ))]),
    }
}

/// Type check a global place expression.
fn check_global(module: &Module, name: &str, span: &Span) -> Result<(bool, Type)> {
    module.functions.get(name).map_or(
        Err(vec![Error::UndefinedGlobal(Spanned::new(
            name.to_string(),
            span.clone(),
        ))]),
        |f| Ok((false, f.ty())),
    )
}
