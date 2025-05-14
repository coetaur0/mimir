//! Typing functions.

use std::result;

use crate::{ir::*, source::Spanned};

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

/// Type check a place expression.
fn check_place(module: &Module, locals: &[Local], place: &Spanned<Place>) -> Result<Spanned<Type>> {
    match &place.item {
        Place::Field(place, index) => check_index(module, locals, place, index),
        Place::Deref(place) => check_deref(module, locals, place),
        Place::Global(name) => check_global(module, Spanned::new(name, place.span.clone())),
        Place::Local(id) => Ok(locals[*id].ty.clone()),
    }
}

/// Type check a place index expression.
fn check_index(
    module: &Module,
    locals: &[Local],
    place: &Spanned<Place>,
    index: &Spanned<usize>,
) -> Result<Spanned<Type>> {
    let ty = check_place(module, locals, place)?;
    match ty.item {
        Type::Tuple(elems) if index.item < elems.len() => Ok(elems[index.item].clone()),
        _ => Err(vec![Error::InvalidIndex {
            ty,
            index: index.clone(),
        }]),
    }
}

/// Type check a place dereference expression.
fn check_deref(module: &Module, locals: &[Local], place: &Spanned<Place>) -> Result<Spanned<Type>> {
    let ty = check_place(module, locals, place)?;
    match ty.item {
        Type::Ref(_, _, ty) => Ok(*ty),
        _ => Err(vec![Error::InvalidDeref(ty)]),
    }
}

/// Type check a global place expression.
fn check_global(module: &Module, name: Spanned<&str>) -> Result<Spanned<Type>> {
    module.functions.get(name.item).map_or(
        Err(vec![Error::UndefinedGlobal(Spanned::new(
            name.item.to_string(),
            name.span.clone(),
        ))]),
        |f| Ok(f.ty()),
    )
}

/// Check if a type is a subtype of another.
fn subtype(lhs: &Spanned<Type>, rhs: &Spanned<Type>) -> bool {
    match (&lhs.item, &rhs.item) {
        (Type::Fn(lparams, lresult), Type::Fn(rparams, rresult)) => {
            lparams.len() == rparams.len()
                && lparams.iter().zip(rparams).all(|(l, r)| subtype(r, l))
                && subtype(lresult, rresult)
        }
        (Type::Ref(lorigin, lmut, lty), Type::Ref(rorigin, rmut, rty)) => {
            (rorigin.is_some_and(|rid| lorigin.is_some_and(|lid| lid == rid)) || rorigin.is_none())
                && (*rmut || !*lmut)
                && subtype(lty, rty)
        }
        (Type::Tuple(lelems), Type::Tuple(relems)) => {
            lelems.len() == relems.len() && lelems.iter().zip(relems).all(|(l, r)| subtype(l, r))
        }
        (lty, rty) => lty == rty,
    }
}
