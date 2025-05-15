//! AST to IR lowering functions.

use std::{collections::HashMap, result};

use crate::{
    ast,
    ir::{self, LocalId, OriginId},
    source::{Span, Spanned},
};

/// Lower an AST module to its IR representation.
pub fn lower(module: &ast::Module) -> Result<ir::Module> {
    Lowerer::lower(module)
}

/// An AST lowering result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// An AST lowering error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    DuplicateFunction(String),
    DuplicateOrigin(Spanned<String>),
    DuplicateParameter(Spanned<String>),
    InvalidOrigin(Spanned<String>),
}

/// An AST to IR lowerer.
struct Lowerer<'mdl> {
    origin_ids: HashMap<&'mdl str, OriginId>,
    local_ids: HashMap<&'mdl str, LocalId>,
    locals: Vec<ir::Local>,
}

impl<'mdl> Lowerer<'mdl> {
    /// Lower an AST module to its IR representation.
    fn lower(module: &'mdl ast::Module) -> Result<ir::Module> {
        let mut lowerer = Lowerer {
            origin_ids: HashMap::new(),
            local_ids: HashMap::new(),
            locals: Vec::new(),
        };

        let mut functions = HashMap::new();
        let mut errors = Vec::new();
        for (name, function) in &module.functions {
            match lowerer.function(function) {
                Ok(ir_function) => {
                    if functions.insert(name.clone(), ir_function).is_some() {
                        errors.push(Error::DuplicateFunction(name.clone()));
                    }
                }
                Err(errs) => errors.extend(errs),
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(ir::Module { functions })
    }

    /// Lower an AST function to its IR representation.
    fn function(&mut self, function: &'mdl ast::Function) -> Result<ir::Function> {
        self.origin_ids.clear();
        self.local_ids.clear();
        self.locals.clear();
        let mut errors = Vec::new();

        let origins: Vec<String> = function
            .origins
            .iter()
            .enumerate()
            .map(|(i, o)| {
                if self.origin_ids.insert(&o.item, i).is_some() {
                    errors.push(Error::DuplicateOrigin(o.clone()));
                };
                o.item.clone()
            })
            .collect();

        self.locals.push(ir::Local {
            mutable: true,
            name: None,
            ty: self.ty(&function.result)?,
        });
        for (i, param) in function.params.iter().enumerate() {
            if self.local_ids.insert(&param.name.item, i + 1).is_some() {
                errors.push(Error::DuplicateParameter(param.name.clone()));
            } else {
                match self.local(param) {
                    Ok(local) => self.locals.push(local),
                    Err(errs) => errors.extend(errs),
                };
            }
        }

        if errors.is_empty() {
            let body = self.block(&function.body)?;
            Ok(ir::Function {
                origins,
                locals: self.locals.clone(),
                param_count: function.params.len(),
                body,
            })
        } else {
            Err(errors)
        }
    }

    /// Lower an AST local declaration to its IR representation.
    fn local(&self, local: &ast::Local) -> Result<ir::Local> {
        let ty = self.ty(&local.ty)?;
        Ok(ir::Local {
            mutable: local.mutable,
            name: Some(local.name.clone()),
            ty,
        })
    }

    /// Lower an AST type to its IR representation.
    fn ty(&self, ty: &Spanned<ast::Type>) -> Result<Spanned<ir::Type>> {
        match &ty.item {
            ast::Type::Fn(params, result) => self.fn_ty(params, result, &ty.span),
            ast::Type::Ref(origin, is_mut, ty) => self.ref_ty(origin, *is_mut, ty, &ty.span),
            ast::Type::Tuple(elems) => self.tuple_ty(elems, &ty.span),
            ast::Type::I32 => Ok(Spanned::new(ir::Type::I32, ty.span.clone())),
            ast::Type::Bool => Ok(Spanned::new(ir::Type::Bool, ty.span.clone())),
        }
    }

    /// Lower a function type to its IR representation.
    fn fn_ty(
        &self,
        params: &[Spanned<ast::Type>],
        result: &Spanned<ast::Type>,
        span: &Span,
    ) -> Result<Spanned<ir::Type>> {
        let mut tys = Vec::new();
        let mut errors = Vec::new();

        for ty in params {
            match self.ty(ty) {
                Ok(ty) => tys.push(ty),
                Err(errs) => errors.extend(errs),
            }
        }

        match self.ty(result) {
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
    fn ref_ty(
        &self,
        origin: &Option<Spanned<String>>,
        mutable: bool,
        ty: &Spanned<ast::Type>,
        span: &Span,
    ) -> Result<Spanned<ir::Type>> {
        let origin_id = if let Some(name) = origin {
            self.origin_ids
                .get::<str>(&name.item)
                .map_or(Err(vec![Error::InvalidOrigin(name.clone())]), |id| {
                    Ok(Some(*id))
                })?
        } else {
            None
        };
        let ir_ty = self.ty(ty)?;
        Ok(Spanned::new(
            ir::Type::Ref(origin_id, mutable, Box::new(ir_ty)),
            span.clone(),
        ))
    }

    /// Lower a tuple type to its IR representation.
    fn tuple_ty(&self, elems: &[Spanned<ast::Type>], span: &Span) -> Result<Spanned<ir::Type>> {
        let mut tys = Vec::new();
        let mut errors = Vec::new();

        for ty in elems {
            match self.ty(ty) {
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
    fn block(&mut self, block: &Spanned<ast::Block>) -> Result<Spanned<ir::Block>> {
        todo!()
    }
}
