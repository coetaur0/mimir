//! Typing functions.

use std::result;

use crate::{
    ir::{self, Block, Function, Instruction, Local, Module, Operand, OriginId, Place},
    source::{Span, Spanned},
};

/// Type check an IR module.
pub fn check(module: &Module) -> Result<()> {
    TypeChecker::check(module)
}

/// A typing result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A typing error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    IncompatibleTypes {
        expected: Spanned<Type>,
        found: Type,
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

/// A type checker for Mimir.
struct TypeChecker<'mdl> {
    module: &'mdl Module,
    n_origins: usize,
    locals: &'mdl [Local],
}

impl<'mdl> TypeChecker<'mdl> {
    /// Type check some IR module.
    fn check(module: &'mdl Module) -> Result<()> {
        let mut ty_checker = TypeChecker {
            module,
            n_origins: 0,
            locals: &[],
        };

        let mut errors = Vec::new();
        for function in module.functions.values() {
            ty_checker
                .function(function)
                .unwrap_or_else(|errs| errors.extend(errs));
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Type check a function declaration.
    fn function(&mut self, function: &'mdl Function) -> Result<()> {
        self.n_origins = function.origins.len();
        self.locals = &function.locals;

        let mut errors = Vec::new();
        for local in &function.locals {
            self.ty(&local.ty)
                .unwrap_or_else(|errs| errors.extend(errs));
        }
        self.block(&function.body)
            .unwrap_or_else(|errs| errors.extend(errs));

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Check if a type is well-formed.
    fn ty(&self, ty: &Spanned<ir::Type>) -> Result<()> {
        match &ty.item {
            ir::Type::Fn(params, result) => self.fn_ty(params, result),
            ir::Type::Ref(origin, _, ty) => {
                if origin.is_some() && origin.unwrap() >= self.n_origins {
                    return Err(vec![Error::InvalidOrigin(ty.span.clone())]);
                }
                self.ty(ty)
            }
            ir::Type::Tuple(elems) => self.tuple_ty(elems),
            ir::Type::I32 => Ok(()),
            ir::Type::Bool => Ok(()),
        }
    }

    /// Check if a function type is well formed.
    fn fn_ty(&self, params: &Vec<Spanned<ir::Type>>, result: &Spanned<ir::Type>) -> Result<()> {
        let mut errors = Vec::new();
        self.tuple_ty(params)
            .unwrap_or_else(|errs| errors.extend(errs));
        self.ty(result).unwrap_or_else(|errs| errors.extend(errs));
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Check if a tuple type is well-formed.
    fn tuple_ty(&self, elems: &Vec<Spanned<ir::Type>>) -> Result<()> {
        let mut errors = Vec::new();
        for elem in elems {
            self.ty(elem).unwrap_or_else(|errs| errors.extend(errs));
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Type check a block of instructions.
    fn block(&self, block: &Block) -> Result<()> {
        let mut errors = Vec::new();
        for instr in block {
            self.instr(instr).unwrap_or_else(|errs| errors.extend(errs));
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Type check an instruction.
    fn instr(&self, instr: &Instruction) -> Result<()> {
        match &instr {
            Instruction::If(cond, then, els) => self.conditional_instr(cond, then, els),
            Instruction::Call(target, callee, args) => self.call_instr(target, callee, args),
            Instruction::Borrow(target, mutable, place) => {
                self.borrow_instr(target, *mutable, place)
            }
            Instruction::Value(target, operand) => self.value_instr(target, operand),
            Instruction::Return => Ok(()),
        }
    }

    /// Type check a conditional instruction.
    fn conditional_instr(&self, cond: &Spanned<Operand>, then: &Block, els: &Block) -> Result<()> {
        match self.operand(cond)? {
            Type::Bool => {
                self.block(then)?;
                self.block(els)?;
                Ok(())
            }
            ty => Err(vec![Error::InvalidCondition(Spanned::new(
                ty,
                cond.span.clone(),
            ))]),
        }
    }

    /// Type check a call instruction.
    fn call_instr(
        &self,
        target: &Spanned<Place>,
        callee: &Spanned<Place>,
        args: &[Spanned<Operand>],
    ) -> Result<()> {
        match self.place(callee)?.1 {
            Type::Fn(params, result) => {
                if args.len() != params.len() {
                    return Err(vec![Error::InvalidArgNum(Spanned::new(
                        args.len(),
                        callee.span.clone(),
                    ))]);
                }

                let mut errors = Vec::new();
                for (arg, param) in args.iter().zip(params) {
                    match self.operand(arg) {
                        Ok(ty) if ty.subtype_of(&param) => (),
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

                let (_, target_ty) = self.place(target)?;
                if result.subtype_of(&target_ty) {
                    Ok(())
                } else {
                    Err(vec![Error::IncompatibleTypes {
                        expected: Spanned::new(target_ty, target.span.clone()),
                        found: *result,
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
    fn borrow_instr(
        &self,
        target: &Spanned<Place>,
        mutable: bool,
        place: &Spanned<Place>,
    ) -> Result<()> {
        let (_, target_ty) = self.place(target)?;
        let (place_mut, place_ty) = self.place(place)?;
        let ref_ty = Type::Ref(None, mutable, Box::new(place_ty));
        if mutable && !place_mut {
            Err(vec![Error::UnauthorizedBorrow(place.span.clone())])
        } else if !ref_ty.subtype_of(&target_ty) {
            Err(vec![Error::IncompatibleTypes {
                expected: Spanned::new(target_ty, target.span.clone()),
                found: ref_ty,
            }])
        } else {
            Ok(())
        }
    }

    /// Type check an assignment instruction.
    fn value_instr(&self, target: &Spanned<Place>, value: &Spanned<Operand>) -> Result<()> {
        let (_, target_ty) = self.place(target)?;
        let value_ty = self.operand(value)?;
        if !value_ty.subtype_of(&target_ty) {
            Err(vec![Error::IncompatibleTypes {
                expected: Spanned::new(target_ty, target.span.clone()),
                found: value_ty,
            }])
        } else {
            Ok(())
        }
    }

    /// Type check an instruction operand.
    fn operand(&self, operand: &Spanned<Operand>) -> Result<Type> {
        match &operand.item {
            Operand::Tuple(elems) => self.tuple_operand(elems),
            Operand::Place(place) => Ok(self
                .place(&Spanned::new(place.clone(), operand.span.clone()))?
                .1),
            Operand::Int(_) => Ok(Type::I32),
            Operand::Bool(_) => Ok(Type::Bool),
        }
    }

    /// Type check a tuple operand.
    fn tuple_operand(&self, elems: &Vec<Spanned<Operand>>) -> Result<Type> {
        let mut types = Vec::new();
        let mut errors = Vec::new();
        for op in elems {
            match self.operand(op) {
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
    fn place(&self, place: &Spanned<Place>) -> Result<(bool, Type)> {
        match &place.item {
            Place::Field(place, index) => self.index_place(place, index),
            Place::Deref(place) => self.deref_place(place),
            Place::Global(name) => self.global_place(name, &place.span),
            Place::Local(id) => self.local_place(*id, &place.span),
        }
    }

    /// Type check a place index expression.
    fn index_place(&self, place: &Spanned<Place>, index: &Spanned<usize>) -> Result<(bool, Type)> {
        let (is_mut, ty) = self.place(place)?;
        match ty {
            Type::Tuple(elems) if index.item < elems.len() => {
                Ok((is_mut, elems[index.item].clone()))
            }
            _ => Err(vec![Error::InvalidIndex {
                ty: Spanned::new(ty, place.span.clone()),
                index: index.clone(),
            }]),
        }
    }

    /// Type check a place dereference expression.
    fn deref_place(&self, place: &Spanned<Place>) -> Result<(bool, Type)> {
        let (_, ty) = self.place(place)?;
        match ty {
            Type::Ref(_, is_mut, ty) => Ok((is_mut, *ty)),
            _ => Err(vec![Error::InvalidDeref(Spanned::new(
                ty,
                place.span.clone(),
            ))]),
        }
    }

    /// Type check a global place expression.
    fn global_place(&self, name: &str, span: &Span) -> Result<(bool, Type)> {
        self.module.functions.get(name).map_or(
            Err(vec![Error::UndefinedGlobal(Spanned::new(
                name.to_string(),
                span.clone(),
            ))]),
            |f| Ok((false, f.ty())),
        )
    }

    /// Type check a local place expression.
    fn local_place(&self, id: usize, span: &Span) -> Result<(bool, Type)> {
        if id >= self.locals.len() {
            return Err(vec![Error::UndefinedLocal(span.clone())]);
        }
        Ok((self.locals[id].mutable, (&self.locals[id].ty).into()))
    }
}
