//! AST to IR lowering functions.

use std::{collections::HashMap, result};

use crate::{
    ast,
    ir::{self, Local, LocalId, OriginId},
    source::{Span, Spanned},
};

/// A lowering result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A lowering error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    DuplicateOrigin(Spanned<String>),
    DuplicateParameter(Spanned<String>),
    InvalidOrigin(Spanned<String>),
}

/// Lower an AST function to its IR representation.
fn lower_function(function: &ast::Function) -> Result<ir::Function> {
    let mut errors = Vec::new();

    let mut origin_ids = HashMap::new();
    let origins: Vec<String> = function
        .origins
        .iter()
        .enumerate()
        .map(|(i, o)| {
            if origin_ids.insert(o.item.clone(), i).is_some() {
                errors.push(Error::DuplicateOrigin(o.clone()));
            };
            o.item.clone()
        })
        .collect();

    let mut local_ids = HashMap::new();
    let mut locals = vec![ir::Local {
        mutable: true,
        name: None,
        ty: lower_ty(&origin_ids, &function.result)?,
    }];
    for (i, param) in function.params.iter().enumerate() {
        if local_ids.insert(param.name.item.clone(), i + 1).is_some() {
            errors.push(Error::DuplicateParameter(param.name.clone()));
        } else {
            match lower_local(&origin_ids, param) {
                Ok(local) => locals.push(local),
                Err(errs) => errors.extend(errs),
            };
        }
    }

    if errors.is_empty() {
        let body = lower_block(&origin_ids, &mut local_ids, &mut locals, &function.body)?;
        Ok(ir::Function {
            origins,
            locals,
            param_count: function.params.len(),
            body,
        })
    } else {
        Err(errors)
    }
}

/// Lower an AST local declaration to its IR representation.
fn lower_local(origin_ids: &HashMap<String, OriginId>, local: &ast::Local) -> Result<ir::Local> {
    let ty = lower_ty(origin_ids, &local.ty)?;
    Ok(ir::Local {
        mutable: local.mutable,
        name: Some(local.name.clone()),
        ty,
    })
}

/// Lower an AST type to its IR representation.
fn lower_ty(
    origin_ids: &HashMap<String, OriginId>,
    ty: &Spanned<ast::Type>,
) -> Result<Spanned<ir::Type>> {
    match &ty.item {
        ast::Type::Fn(params, result) => lower_fn_ty(origin_ids, params, result, &ty.span),
        ast::Type::Ref(origin, is_mut, ty) => {
            lower_ref_ty(origin_ids, origin, *is_mut, ty, &ty.span)
        }
        ast::Type::Tuple(elems) => lower_tuple_ty(origin_ids, elems, &ty.span),
        ast::Type::I32 => Ok(Spanned::new(ir::Type::I32, ty.span.clone())),
        ast::Type::Bool => Ok(Spanned::new(ir::Type::Bool, ty.span.clone())),
    }
}

/// Lower a function type to its IR representation.
fn lower_fn_ty(
    origin_ids: &HashMap<String, OriginId>,
    params: &[Spanned<ast::Type>],
    result: &Spanned<ast::Type>,
    span: &Span,
) -> Result<Spanned<ir::Type>> {
    let mut tys = Vec::new();
    let mut errors = Vec::new();

    for ty in params {
        match lower_ty(origin_ids, ty) {
            Ok(ty) => tys.push(ty),
            Err(errs) => errors.extend(errs),
        }
    }

    match lower_ty(origin_ids, result) {
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
    origin_ids: &HashMap<String, OriginId>,
    origin: &Option<Spanned<String>>,
    mutable: bool,
    ty: &Spanned<ast::Type>,
    span: &Span,
) -> Result<Spanned<ir::Type>> {
    let origin_id = if let Some(name) = origin {
        origin_ids
            .get(&name.item)
            .map_or(Err(vec![Error::InvalidOrigin(name.clone())]), |id| {
                Ok(Some(*id))
            })?
    } else {
        None
    };
    let ir_ty = lower_ty(origin_ids, ty)?;
    Ok(Spanned::new(
        ir::Type::Ref(origin_id, mutable, Box::new(ir_ty)),
        span.clone(),
    ))
}

/// Lower a tuple type to its IR representation.
fn lower_tuple_ty(
    origin_ids: &HashMap<String, OriginId>,
    elems: &[Spanned<ast::Type>],
    span: &Span,
) -> Result<Spanned<ir::Type>> {
    let mut tys = Vec::new();
    let mut errors = Vec::new();

    for ty in elems {
        match lower_ty(origin_ids, ty) {
            Ok(ty) => tys.push(ty),
            Err(errs) => errors.extend(errs),
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Spanned::new(ir::Type::Tuple(tys), span.clone()))
}

/// Lower an AST block expression to its IR representation.
fn lower_block(
    origin_ids: &HashMap<String, OriginId>,
    local_ids: &mut HashMap<String, LocalId>,
    locals: &mut [Local],
    block: &Spanned<ast::Block>,
) -> Result<Spanned<ir::Block>> {
    todo!()
}
