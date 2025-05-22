//! Type checking functions.

use crate::{
    ir::*,
    reporting::{Error, Result, Span, Spanned},
};

/// Type check an IR module.
pub fn check(module: &Module) -> Result<()> {
    TypeChecker::check(module)
}

/// A type checker for Mimir.
struct TypeChecker<'m> {
    module: &'m Module,
    origin_count: usize,
    locals: &'m [Local],
}

impl<'m> TypeChecker<'m> {
    /// Type check some IR module.
    fn check(module: &'m Module) -> Result<()> {
        let mut ty_checker = TypeChecker {
            module,
            origin_count: 0,
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
    fn function(&mut self, function: &'m Function) -> Result<()> {
        self.origin_count = function.origin_count;
        self.locals = &function.locals;
        let mut errors = Vec::new();

        for (i, local) in function.locals.iter().enumerate() {
            self.ty(&local.ty, i <= function.param_count)
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
    fn ty(&self, ty: &Spanned<Type>, with_origins: bool) -> Result<()> {
        match &ty.item {
            Type::Fn(params, result) => self.fn_ty(params, result),
            Type::Ref(origin, _, ty) => {
                if with_origins && origin.is_none() {
                    return Err(vec![Error::OriginNeeded(ty.span.clone())]);
                }
                if origin.is_some() && origin.unwrap() >= self.origin_count {
                    return Err(vec![Error::UndefinedOrigin(ty.span.clone())]);
                }
                self.ty(ty, with_origins)
            }
            Type::Tuple(elems) => self.tuple_ty(elems, with_origins),
            Type::I32 => Ok(()),
            Type::Bool => Ok(()),
        }
    }

    /// Check if a function type is well formed.
    fn fn_ty(&self, params: &Vec<Spanned<Type>>, result: &Spanned<Type>) -> Result<()> {
        let mut errors = Vec::new();

        self.tuple_ty(params, false)
            .unwrap_or_else(|errs| errors.extend(errs));
        self.ty(result, false)
            .unwrap_or_else(|errs| errors.extend(errs));

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Check if a tuple type is well-formed.
    fn tuple_ty(&self, elems: &Vec<Spanned<Type>>, with_origins: bool) -> Result<()> {
        let mut errors = Vec::new();

        for elem in elems {
            self.ty(elem, with_origins)
                .unwrap_or_else(|errs| errors.extend(errs));
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
        match self.operand(cond)?.item {
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
        match self.place(callee)?.1.item {
            Type::Fn(params, result) => {
                if args.len() != params.len() {
                    return Err(vec![Error::InvalidArgNum(
                        params.len(),
                        Spanned::new(args.len(), callee.span.clone()),
                    )]);
                }

                let mut errors = Vec::new();
                for (arg, param) in args.iter().zip(params) {
                    match self.operand(arg) {
                        Ok(ty) if ty.subtype_of(&param) => (),
                        Ok(ty) => errors.push(Error::InvalidArg(
                            param.item,
                            Spanned::new(ty.item.clone(), arg.span.clone()),
                        )),
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
                    Err(vec![Error::IncompatibleTypes(
                        target_ty.item,
                        Spanned::new(result.item.clone(), callee.span.clone()),
                    )])
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
        let ref_ty = Spanned::new(
            Type::Ref(None, mutable, Box::new(place_ty)),
            target.span.clone(),
        );
        if mutable && !place_mut {
            Err(vec![Error::UnauthorizedBorrow(place.span.clone())])
        } else if !ref_ty.subtype_of(&target_ty) {
            Err(vec![Error::IncompatibleTypes(
                target_ty.item,
                Spanned::new(ref_ty.item.clone(), place.span.clone()),
            )])
        } else {
            Ok(())
        }
    }

    /// Type check an assignment instruction.
    fn value_instr(&self, target: &Spanned<Place>, value: &Spanned<Operand>) -> Result<()> {
        let (_, target_ty) = self.place(target)?;
        let value_ty = self.operand(value)?;
        if !value_ty.subtype_of(&target_ty) {
            Err(vec![Error::IncompatibleTypes(
                target_ty.item,
                Spanned::new(value_ty.item.clone(), value.span.clone()),
            )])
        } else {
            Ok(())
        }
    }

    /// Type check an instruction operand.
    fn operand(&self, operand: &Spanned<Operand>) -> Result<Spanned<Type>> {
        match &operand.item {
            Operand::Tuple(elems) => self.tuple_operand(elems, &operand.span),
            Operand::Place(place) => Ok(self
                .place(&Spanned::new(place.clone(), operand.span.clone()))?
                .1),
            Operand::Int(_) => Ok(Spanned::new(Type::I32, operand.span.clone())),
            Operand::Bool(_) => Ok(Spanned::new(Type::Bool, operand.span.clone())),
        }
    }

    /// Type check a tuple operand.
    fn tuple_operand(&self, elems: &Vec<Spanned<Operand>>, span: &Span) -> Result<Spanned<Type>> {
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
        Ok(Spanned::new(Type::Tuple(types), span.clone()))
    }

    /// Type check a place expression.
    fn place(&self, place: &Spanned<Place>) -> Result<(bool, Spanned<Type>)> {
        match &place.item {
            Place::Field(place, index) => self.index_place(place, index),
            Place::Deref(place) => self.deref_place(place),
            Place::Global(name, args) => self.global_place(name, args),
            Place::Local(id) => self.local_place(*id, &place.span),
        }
    }

    /// Type check a place index expression.
    fn index_place(
        &self,
        place: &Spanned<Place>,
        index: &Spanned<usize>,
    ) -> Result<(bool, Spanned<Type>)> {
        let (is_mut, ty) = self.place(place)?;
        match ty.item {
            Type::Tuple(elems) if index.item < elems.len() => {
                Ok((is_mut, elems[index.item].clone()))
            }
            _ => Err(vec![Error::InvalidField(ty, index.clone())]),
        }
    }

    /// Type check a place dereference expression.
    fn deref_place(&self, place: &Spanned<Place>) -> Result<(bool, Spanned<Type>)> {
        let (_, ty) = self.place(place)?;
        match ty.item {
            Type::Ref(_, is_mut, ty) => Ok((is_mut, *ty)),
            _ => Err(vec![Error::InvalidDeref(ty)]),
        }
    }

    /// Type check a global place expression.
    fn global_place(
        &self,
        name: &Spanned<String>,
        args: &[Option<OriginId>],
    ) -> Result<(bool, Spanned<Type>)> {
        match self.module.functions.get(&name.item) {
            Some(f) => {
                if args.len() != f.origin_count {
                    return Err(vec![Error::InvalidOriginArgNum(
                        name.clone(),
                        f.origin_count,
                        args.len(),
                    )]);
                }
                Ok((false, f.ty().substitute(args)))
            }
            None => Err(vec![Error::UndefinedGlobal(name.clone())]),
        }
    }

    /// Type check a local place expression.
    fn local_place(&self, id: usize, span: &Span) -> Result<(bool, Spanned<Type>)> {
        if id >= self.locals.len() {
            return Err(vec![Error::UndefinedLocal(span.clone())]);
        }
        Ok((self.locals[id].mutable, self.locals[id].ty.clone()))
    }
}
