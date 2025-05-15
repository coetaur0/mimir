//! Typing functions.

use std::result;

use crate::{
    ir::{self, Block, Function, Instruction, Local, Module, Operand, OriginId, Place},
    source::{Span, Spanned},
};

/// Type check an IR module.
pub fn check(module: &Module) -> Result<()> {
    let mut errors = Vec::new();
    for function in module.functions.values() {
        check_function(module, function).unwrap_or_else(|errs| errors.extend(errs));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(())
}

/// A typing result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A typing error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    IncompatibleTypes {
        target: Spanned<Type>,
        value: Type,
    },
    InvalidArg {
        found: Spanned<Type>,
        expected: Type,
    },
    InvalidIndex {
        ty: Spanned<Type>,
        index: Spanned<usize>,
    },
    InvalidOrigin(Span),
    InvalidCondition(Spanned<Type>),
    InvalidCallee(Spanned<Type>),
    InvalidArgNum(Spanned<usize>),
    UnauthorizedBorrow(Span),
    InvalidDeref(Spanned<Type>),
    UndefinedGlobal(Spanned<String>),
    UndefinedLocal(Span),
}

/// A (semantic) type.
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

/// Type check a function declaration.
fn check_function(module: &Module, function: &Function) -> Result<()> {
    let mut errors = Vec::new();
    for local in &function.locals {
        check_ty(function.origins.len(), &local.ty).unwrap_or_else(|errs| errors.extend(errs));
    }
    check_block(module, &function.locals, &function.body)
        .unwrap_or_else(|errs| errors.extend(errs));
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(())
}

/// Check if a type is well-formed.
fn check_ty(origins: usize, ty: &Spanned<ir::Type>) -> Result<()> {
    match &ty.item {
        ir::Type::Fn(params, result) => check_fn_ty(origins, params, result),
        ir::Type::Ref(origin, _, ty) => {
            if origin.is_some() && origin.unwrap() >= origins {
                return Err(vec![Error::InvalidOrigin(ty.span.clone())]);
            }
            check_ty(origins, ty)
        }
        ir::Type::Tuple(elems) => check_tuple_ty(origins, elems),
        ir::Type::I32 => Ok(()),
        ir::Type::Bool => Ok(()),
    }
}

/// Check if a function type is well formed.
fn check_fn_ty(
    origins: usize,
    params: &Vec<Spanned<ir::Type>>,
    result: &Spanned<ir::Type>,
) -> Result<()> {
    let mut errors = Vec::new();
    check_tuple_ty(origins, params).unwrap_or_else(|errs| errors.extend(errs));
    check_ty(origins, result).unwrap_or_else(|errs| errors.extend(errs));
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(())
}

/// Check if a tuple type is well-formed.
fn check_tuple_ty(origins: usize, elems: &Vec<Spanned<ir::Type>>) -> Result<()> {
    let mut errors = Vec::new();
    for elem in elems {
        check_ty(origins, elem).unwrap_or_else(|errs| errors.extend(errs));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(())
}

/// Type check a block of instructions.
fn check_block(module: &Module, locals: &[Local], block: &Spanned<Block>) -> Result<()> {
    let mut errors = Vec::new();
    for instr in &block.item {
        check_instr(module, locals, instr).unwrap_or_else(|errs| errors.extend(errs));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(())
}

/// Type check an instruction.
fn check_instr(module: &Module, locals: &[Local], instr: &Spanned<Instruction>) -> Result<()> {
    match &instr.item {
        Instruction::If(cond, then, els) => check_if(module, locals, cond, then, els),
        Instruction::Call(target, callee, args) => check_call(module, locals, target, callee, args),
        Instruction::Borrow(target, mutable, place) => {
            check_borrow(module, locals, target, *mutable, place)
        }
        Instruction::Value(target, operand) => check_value(module, locals, target, operand),
        Instruction::Return => Ok(()),
    }
}

/// Type check a conditional instruction.
fn check_if(
    module: &Module,
    locals: &[Local],
    cond: &Spanned<Operand>,
    then: &Spanned<Block>,
    els: &Spanned<Block>,
) -> Result<()> {
    match check_operand(module, locals, cond)? {
        Type::Bool => {
            check_block(module, locals, then)?;
            check_block(module, locals, els)?;
            Ok(())
        }
        ty => Err(vec![Error::InvalidCondition(Spanned::new(
            ty,
            cond.span.clone(),
        ))]),
    }
}

/// Type check a call instruction.
fn check_call(
    module: &Module,
    locals: &[Local],
    target: &Spanned<Place>,
    callee: &Spanned<Place>,
    args: &[Spanned<Operand>],
) -> Result<()> {
    match check_place(module, locals, callee)?.1 {
        Type::Fn(params, result) => {
            if args.len() != params.len() {
                return Err(vec![Error::InvalidArgNum(Spanned::new(
                    args.len(),
                    callee.span.clone(),
                ))]);
            }

            let mut errors = Vec::new();
            for (arg, param) in args.iter().zip(params) {
                match check_operand(module, locals, arg) {
                    Ok(ty) if ty == param => (),
                    Ok(ty) => errors.push(Error::InvalidArg {
                        found: Spanned::new(ty, arg.span.clone()),
                        expected: param,
                    }),
                    Err(errs) => errors.extend(errs),
                }
            }
            if !errors.is_empty() {
                return Err(errors);
            }

            let (_, target_ty) = check_place(module, locals, target)?;
            if result.subtype_of(&target_ty) {
                Ok(())
            } else {
                Err(vec![Error::IncompatibleTypes {
                    target: Spanned::new(target_ty, target.span.clone()),
                    value: *result,
                }])
            }
        }
        ty => Err(vec![Error::InvalidCallee(Spanned::new(
            ty,
            callee.span.clone(),
        ))]),
    }
}

/// Type check a borrow instruction.
fn check_borrow(
    module: &Module,
    locals: &[Local],
    target: &Spanned<Place>,
    mutable: bool,
    place: &Spanned<Place>,
) -> Result<()> {
    let (_, target_ty) = check_place(module, locals, target)?;
    let (place_mut, place_ty) = check_place(module, locals, place)?;
    let ref_ty = Type::Ref(None, mutable, Box::new(place_ty));
    if mutable && !place_mut {
        Err(vec![Error::UnauthorizedBorrow(place.span.clone())])
    } else if !ref_ty.subtype_of(&target_ty) {
        Err(vec![Error::IncompatibleTypes {
            target: Spanned::new(target_ty, target.span.clone()),
            value: ref_ty,
        }])
    } else {
        Ok(())
    }
}

/// Type check an assignment instruction.
fn check_value(
    module: &Module,
    locals: &[Local],
    target: &Spanned<Place>,
    value: &Spanned<Operand>,
) -> Result<()> {
    let (_, target_ty) = check_place(module, locals, target)?;
    let value_ty = check_operand(module, locals, value)?;
    if !value_ty.subtype_of(&target_ty) {
        Err(vec![Error::IncompatibleTypes {
            target: Spanned::new(target_ty, target.span.clone()),
            value: value_ty,
        }])
    } else {
        Ok(())
    }
}

/// Type check an instruction operand.
fn check_operand(module: &Module, locals: &[Local], operand: &Spanned<Operand>) -> Result<Type> {
    match &operand.item {
        Operand::Tuple(elems) => check_tuple(module, locals, elems),
        Operand::Place(place) => Ok(check_place(
            module,
            locals,
            &Spanned::new(place.clone(), operand.span.clone()),
        )?
        .1),
        Operand::Int(_) => Ok(Type::I32),
        Operand::Bool(_) => Ok(Type::Bool),
    }
}

/// Type check a tuple operand.
fn check_tuple(module: &Module, locals: &[Local], elems: &Vec<Spanned<Operand>>) -> Result<Type> {
    let mut types = Vec::new();
    let mut errors = Vec::new();

    for op in elems {
        match check_operand(module, locals, op) {
            Ok(ty) => types.push(ty),
            Err(errs) => errors.extend(errs),
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Type::Tuple(types))
}

/// Type check a place expression.
fn check_place(module: &Module, locals: &[Local], place: &Spanned<Place>) -> Result<(bool, Type)> {
    match &place.item {
        Place::Field(place, index) => check_index(module, locals, place, index),
        Place::Deref(place) => check_deref(module, locals, place),
        Place::Global(name) => check_global(module, name, &place.span),
        Place::Local(id) => check_local(locals, *id, &place.span),
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

/// Type check a local place expression.
fn check_local(locals: &[Local], id: usize, span: &Span) -> Result<(bool, Type)> {
    if id >= locals.len() {
        return Err(vec![Error::UndefinedLocal(span.clone())]);
    }
    Ok((locals[id].mutable, (&locals[id].ty).into()))
}
