//! Type checking functions.

use std::result;

use ariadne::{Color, Label, Report, ReportKind, Source};

use crate::{Diagnostic, Span, Spanned, ir::*};

/// Type check an IR module.
pub fn check(module: &Module) -> Result<()> {
    TypeChecker::check(module)
}

/// Substitute the origin ids in a type.
pub fn substitute(ty: &Spanned<Type>, subst: &[Option<OriginId>]) -> Spanned<Type> {
    match &ty.item {
        Type::Fn(params, result) => Spanned::new(
            Type::Fn(
                params.iter().map(|p| substitute(p, subst)).collect(),
                Box::new(substitute(result, subst)),
            ),
            ty.span.clone(),
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
                Type::Ref(new_origin, *mutability, Box::new(substitute(ref_ty, subst))),
                ty.span.clone(),
            )
        }
        Type::Tuple(elems) => Spanned::new(
            Type::Tuple(elems.iter().map(|e| substitute(e, subst)).collect()),
            ty.span.clone(),
        ),
        Type::I32 | Type::Bool => ty.clone(),
    }
}

/// A type checking result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// A type checking error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    IncompatibleTypes {
        expected: Type,
        found: Spanned<Type>,
    },
    InvalidArg {
        expected: Type,
        found: Spanned<Type>,
    },
    InvalidArgNum {
        expected: usize,
        found: Spanned<usize>,
    },
    InvalidCallee(Spanned<Type>),
    InvalidCondition(Spanned<Type>),
    InvalidDeref(Spanned<Type>),
    InvalidField {
        ty: Type,
        index: Spanned<usize>,
    },
    InvalidOriginArgNum {
        name: Spanned<String>,
        expected: usize,
        found: usize,
    },
    OriginNeeded(Span),
    UnauthorizedBorrow(Span),
    UndefinedGlobal(Spanned<String>),
    UndefinedLocal(Span),
    UndefinedOrigin(Span),
}

impl Diagnostic for Error {
    fn print(&self, path: &str, contents: &str) {
        match self {
            Error::IncompatibleTypes { expected, found } => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(13)
                    .with_message("Incompatible types.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "expected a value of type {}, but found type {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidArg { expected, found } => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(14)
                    .with_message("Invalid argument type.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "expected a value of type {}, but found type {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidArgNum { expected, found } => {
                Report::build(ReportKind::Error, (path, found.span.clone()))
                    .with_code(15)
                    .with_message("Invalid number of arguments.")
                    .with_label(
                        Label::new((path, found.span.clone()))
                            .with_message(format!(
                                "invalid number of arguments: expected {} but found {}.",
                                expected, found.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidCallee(callee) => {
                Report::build(ReportKind::Error, (path, callee.span.clone()))
                    .with_code(16)
                    .with_message("Invalid callee.")
                    .with_label(
                        Label::new((path, callee.span.clone()))
                            .with_message(format!("cannot call a value of type {}.", callee.item))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidCondition(cond) => {
                Report::build(ReportKind::Error, (path, cond.span.clone()))
                    .with_code(17)
                    .with_message("Invalid condition.")
                    .with_label(
                        Label::new((path, cond.span.clone()))
                            .with_message(format!(
                                "expected a boolean value, but found a value of type {}.",
                                cond.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidDeref(ty) => {
                Report::build(ReportKind::Error, (path, ty.span.clone()))
                    .with_code(18)
                    .with_message("Invalid dereference.")
                    .with_label(
                        Label::new((path, ty.span.clone()))
                            .with_message(format!("cannot dereference a value of type {}.", ty.item))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidField { ty, index } => {
                Report::build(ReportKind::Error, (path, index.span.clone()))
                    .with_code(19)
                    .with_message("Invalid field index.")
                    .with_label(
                        Label::new((path, index.span.clone()))
                            .with_message(format!(
                                "cannot access a value of type {} with index {}.",
                                ty, index.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidOriginArgNum {name, expected, found } => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(20)
                    .with_message("Invalid number of origin arguments.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!("function {} requires {} origin arguments, but {} were found.", name.item, expected, found))
                            .with_color(Color::Red),
                    )
            }
            Error::OriginNeeded(span) => {
                Report::build(ReportKind::Error, (path, span.clone()))
                    .with_code(21)
                    .with_message("No origin specified.")
                    .with_label(
                        Label::new((path, span.clone()))
                            .with_message("references in function signatures need to be annotated with their origin.")
                            .with_color(Color::Red),
                    )
            }
            Error::UnauthorizedBorrow(span) => {
                Report::build(ReportKind::Error, (path, span.clone()))
                    .with_code(22)
                    .with_message("Unauthorized borrow.")
                    .with_label(
                        Label::new((path, span.clone()))
                            .with_message("cannot borrow as mutable.")
                            .with_color(Color::Red),
                    )
            }
            Error::UndefinedGlobal(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(23)
                    .with_message("Undefined function.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!("no function named {} in scope.", name.item))
                            .with_color(Color::Red),
                    )
            }
            Error::UndefinedLocal(span) => {
                Report::build(ReportKind::Error, (path, span.clone()))
                    .with_code(24)
                    .with_message("Undefined variable.")
                    .with_label(
                        Label::new((path, span.clone()))
                            .with_message("unknown variable.")
                            .with_color(Color::Red),
                    )
            }
            Error::UndefinedOrigin(span) => {
                Report::build(ReportKind::Error, (path, span.clone()))
                    .with_code(25)
                    .with_message("Undefined origin.")
                    .with_label(
                        Label::new((path, span.clone()))
                            .with_message("unknown origin.")
                            .with_color(Color::Red),
                    )
            }
        }
        .finish()
        .eprint((path, Source::from(contents)))
        .unwrap()
    }
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
                    return Err(vec![Error::InvalidArgNum {
                        expected: params.len(),
                        found: Spanned::new(args.len(), callee.span.clone()),
                    }]);
                }

                let mut errors = Vec::new();
                for (arg, param) in args.iter().zip(params) {
                    match self.operand(arg) {
                        Ok(ty) if ty.subtype_of(&param) => (),
                        Ok(ty) => errors.push(Error::InvalidArg {
                            found: Spanned::new(ty.item.clone(), arg.span.clone()),
                            expected: param.item,
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
                        expected: target_ty.item,
                        found: Spanned::new(result.item.clone(), callee.span.clone()),
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
        let ref_ty = Spanned::new(
            Type::Ref(None, mutable, Box::new(place_ty)),
            target.span.clone(),
        );
        if mutable && !place_mut {
            Err(vec![Error::UnauthorizedBorrow(place.span.clone())])
        } else if !ref_ty.subtype_of(&target_ty) {
            Err(vec![Error::IncompatibleTypes {
                expected: target_ty.item,
                found: Spanned::new(ref_ty.item.clone(), place.span.clone()),
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
                expected: target_ty.item,
                found: Spanned::new(value_ty.item.clone(), value.span.clone()),
            }])
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
            _ => Err(vec![Error::InvalidField {
                ty: ty.item,
                index: index.clone(),
            }]),
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
                    return Err(vec![Error::InvalidOriginArgNum {
                        name: name.clone(),
                        expected: f.origin_count,
                        found: args.len(),
                    }]);
                }
                Ok((false, substitute(&f.ty(), args)))
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
