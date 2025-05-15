//! AST to IR lowering functions.

use std::{collections::HashMap, result};

use crate::{
    ast,
    ir::{self, OriginId},
    source::{Span, Spanned},
};

/// A lowering result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A lowering error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    InvalidOrigin(Spanned<String>),
}

/// Lower an AST type to its IR representation.
fn lower_ty(
    origins: &HashMap<String, OriginId>,
    ty: &Spanned<ast::Type>,
) -> Result<Spanned<ir::Type>> {
    match &ty.item {
        ast::Type::Fn(params, result) => lower_fn_ty(origins, params, result, &ty.span),
        ast::Type::Ref(origin, is_mut, ty) => lower_ref_ty(origins, origin, *is_mut, ty, &ty.span),
        ast::Type::Tuple(elems) => lower_tuple_ty(origins, elems, &ty.span),
        ast::Type::I32 => Ok(Spanned::new(ir::Type::I32, ty.span.clone())),
        ast::Type::Bool => Ok(Spanned::new(ir::Type::Bool, ty.span.clone())),
    }
}

/// Lower a function type to its IR representation.
fn lower_fn_ty(
    origins: &HashMap<String, OriginId>,
    params: &[Spanned<ast::Type>],
    result: &Spanned<ast::Type>,
    span: &Span,
) -> Result<Spanned<ir::Type>> {
    let mut tys = Vec::new();
    let mut errors = Vec::new();

    for ty in params {
        match lower_ty(origins, ty) {
            Ok(ty) => tys.push(ty),
            Err(errs) => errors.extend(errs),
        }
    }

    match lower_ty(origins, result) {
        Ok(ty) => {
            if !errors.is_empty() {
                return Err(errors);
            }
            Ok(Spanned::new(ir::Type::Fn(tys, Box::new(ty)), span.clone()))
        }
        Err(errs) => {
            errors.extend(errs);
            Err(errors)
        }
    }
}

/// Lower a reference type to its IR representation.
fn lower_ref_ty(
    origins: &HashMap<String, OriginId>,
    origin: &Option<Spanned<String>>,
    mutable: bool,
    ty: &Spanned<ast::Type>,
    span: &Span,
) -> Result<Spanned<ir::Type>> {
    let origin_id = if let Some(name) = origin {
        origins
            .get(&name.item)
            .map_or(Err(vec![Error::InvalidOrigin(name.clone())]), |id| {
                Ok(Some(*id))
            })?
    } else {
        None
    };
    let ir_ty = lower_ty(origins, ty)?;
    Ok(Spanned::new(
        ir::Type::Ref(origin_id, mutable, Box::new(ir_ty)),
        span.clone(),
    ))
}

/// Lower a tuple type to its IR representation.
fn lower_tuple_ty(
    origins: &HashMap<String, OriginId>,
    elems: &[Spanned<ast::Type>],
    span: &Span,
) -> Result<Spanned<ir::Type>> {
    let mut tys = Vec::new();
    let mut errors = Vec::new();

    for ty in elems {
        match lower_ty(origins, ty) {
            Ok(ty) => tys.push(ty),
            Err(errs) => errors.extend(errs),
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Spanned::new(ir::Type::Tuple(tys), span.clone()))
}
