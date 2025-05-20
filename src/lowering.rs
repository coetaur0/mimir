//! AST to IR lowering functions.

use std::{collections::HashMap, mem, result};

use ariadne::{Color, Label, Report, ReportKind, Source};

use crate::{
    ast::{self, Expr, Parameter, Stmt},
    ir::{self, Instruction, Local, LocalId, Operand, OriginId, Place},
    naming::SymbolTable,
    source::{Diagnostic, Span, Spanned},
};

/// Lower an AST module to its IR representation.
pub fn lower(module: &ast::Module) -> Result<ir::Module> {
    let mut lowerer = Lowerer {
        globals: HashMap::new(),
        origin_ids: HashMap::new(),
        local_ids: SymbolTable::new(),
        locals: Vec::new(),
    };
    lowerer.globals(module)?;
    lowerer.module(module)
}

/// An AST lowering result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// An AST lowering error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    DuplicateOrigin(Spanned<String>),
    DuplicateParameter(Spanned<String>),
    InvalidCallee(Span),
    InvalidField(Span, Spanned<usize>),
    InvalidDeref(Span),
    UnassignableExpr(Span),
    UndefinedOrigin(Spanned<String>),
    UndefinedName(Spanned<String>),
    UndefinedType(Spanned<String>),
}

impl Diagnostic for Error {
    fn print(&self, path: &str, contents: &str) {
        match self {
            Error::DuplicateOrigin(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(4)
                    .with_message("Duplicate origin declaration.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "an origin named {} has already been declared in the function.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::DuplicateParameter(name) => {
                Report::build(ReportKind::Error, (path, name.span.clone()))
                    .with_code(5)
                    .with_message("Duplicate parameter declaration.")
                    .with_label(
                        Label::new((path, name.span.clone()))
                            .with_message(format!(
                                "a parameter named {} has already been declared in the function.",
                                name.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidCallee(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(6)
                .with_message("Invalid call expression.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message("invalid callee: an expression of function type is expected.")
                        .with_color(Color::Red),
                ),
            Error::InvalidField(span, index) => {
                Report::build(ReportKind::Error, (path, span.clone()))
                    .with_code(7)
                    .with_message("Invalid field index expression.")
                    .with_label(
                        Label::new((path, index.span.clone()))
                            .with_message(format!(
                                "the expression cannot be accessed with index {}.",
                                index.item
                            ))
                            .with_color(Color::Red),
                    )
            }
            Error::InvalidDeref(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(8)
                .with_message("Invalid dereference expression.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message("this expression cannot be dereferenced.")
                        .with_color(Color::Red),
                ),
            Error::UnassignableExpr(span) => Report::build(ReportKind::Error, (path, span.clone()))
                .with_code(9)
                .with_message("Invalid assignment expression.")
                .with_label(
                    Label::new((path, span.clone()))
                        .with_message("cannot assign to an expression that is not a dereference, a field index or a variable.")
                        .with_color(Color::Red),
                ),
            Error::UndefinedOrigin(name) => Report::build(ReportKind::Error, (path, name.span.clone()))
                .with_code(10)
                .with_message("Undefined origin.")
                .with_label(
                    Label::new((path, name.span.clone()))
                        .with_message(format!(
                            "unknown origin {}.",
                            name.item
                        ))
                        .with_color(Color::Red),
                ),
            Error::UndefinedName(name) => Report::build(ReportKind::Error, (path, name.span.clone()))
                .with_code(11)
                .with_message("Undefined name.")
                .with_label(
                    Label::new((path, name.span.clone()))
                        .with_message(format!(
                            "no function or variable named {} in scope.",
                            name.item
                        ))
                        .with_color(Color::Red),
                ),
            Error::UndefinedType(name) => Report::build(ReportKind::Error, (path, name.span.clone()))
                .with_code(12)
                .with_message("Unkown type.")
                .with_label(
                    Label::new((path, name.span.clone()))
                        .with_message(format!(
                            "cannot determine the type of {}. Annotate the variable with a type or assign it with an initial value.",
                            name.item
                        ))
                        .with_color(Color::Red),
                ),
        }
        .finish()
        .eprint((path, Source::from(contents)))
        .unwrap()
    }
}

/// An AST to IR lowerer.
struct Lowerer<'m> {
    globals: HashMap<&'m str, Spanned<ir::Type>>,
    origin_ids: HashMap<&'m str, OriginId>,
    local_ids: SymbolTable<'m, LocalId>,
    locals: Vec<Local>,
}

impl<'m> Lowerer<'m> {
    /// Initialize the globals table in the lowerer.
    fn globals(&mut self, module: &'m ast::Module) -> Result<()> {
        let mut errors = Vec::new();

        for (name, function) in &module.functions {
            self.origin_ids.clear();
            for (i, origin) in function.origins.iter().enumerate() {
                if self.origin_ids.insert(&origin.item, i).is_some() {
                    errors.push(Error::DuplicateOrigin(origin.clone()));
                }
            }

            match self.ty(&function.ty()) {
                Ok(ty) => {
                    self.globals.insert(name, ty);
                }
                Err(errs) => errors.extend(errs),
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(())
    }

    /// Lower an AST module to its IR representation.
    fn module(&mut self, module: &'m ast::Module) -> Result<ir::Module> {
        let mut functions = HashMap::new();
        let mut errors = Vec::new();

        for (name, function) in &module.functions {
            match self.function(function) {
                Ok(ir_function) => {
                    functions.insert(name.clone(), ir_function);
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
    fn function(&mut self, function: &'m ast::Function) -> Result<ir::Function> {
        self.origin_ids.clear();
        self.local_ids.clear();
        self.locals.clear();
        let mut errors = Vec::new();

        // Lower the function's origin parameters.
        let origins: Vec<String> = function
            .origins
            .iter()
            .enumerate()
            .map(|(i, o)| {
                self.origin_ids.insert(&o.item, i);
                o.item.clone()
            })
            .collect();

        // Lower the function's return type.
        self.locals.push(ir::Local {
            mutable: true,
            ty: self.ty(&function.result)?,
        });

        // Lower the function's parameters.
        for (i, param) in function.params.iter().enumerate() {
            if !self.local_ids.insert(&param.name.item, i + 1) {
                errors.push(Error::DuplicateParameter(param.name.clone()));
            } else {
                match self.parameter(param) {
                    Ok(local) => self.locals.push(local),
                    Err(errs) => errors.extend(errs),
                };
            }
        }

        // Lower the function's body.
        if errors.is_empty() {
            let (mut instrs, op, _) = self.block_expr(&function.body)?;
            let span = op.span.clone();
            // Assign the body's result to the function's return local in the IR.
            instrs.push(Instruction::Value(Spanned::new(Place::Local(0), span), op));
            Ok(ir::Function {
                origins,
                locals: mem::take(&mut self.locals),
                param_count: function.params.len(),
                body: instrs,
            })
        } else {
            Err(errors)
        }
    }

    /// Lower a function parameter declaration to its IR representation.
    fn parameter(&mut self, param: &Parameter) -> Result<Local> {
        let ty = self.ty(&param.ty)?;
        Ok(ir::Local {
            mutable: param.mutable,
            ty,
        })
    }

    /// Lower an AST type to its IR representation.
    fn ty(&self, ty: &Spanned<ast::Type>) -> Result<Spanned<ir::Type>> {
        match &ty.item {
            ast::Type::Fn(params, result) => self.fn_ty(params, result, &ty.span),
            ast::Type::Ref(origin, mutable, r_ty) => self.ref_ty(origin, *mutable, r_ty, &ty.span),
            ast::Type::Tuple(elems) => self.tuple_ty(elems, &ty.span),
            ast::Type::I32 => Ok(Spanned::new(ir::Type::I32, ty.span.clone())),
            ast::Type::Bool => Ok(Spanned::new(ir::Type::Bool, ty.span.clone())),
        }
    }

    /// Lower an AST function type to its IR representation.
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

    /// Lower an AST reference type to its IR representation.
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
                .map_or(Err(vec![Error::UndefinedOrigin(name.clone())]), |id| {
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

    /// Lower an AST statement to its IR representation.
    fn stmt(&mut self, stmt: &'m Spanned<Stmt>) -> Result<ir::Block> {
        match &stmt.item {
            Stmt::Let(mutable, name, ty, value) => self.let_stmt(*mutable, name, ty, value),
            Stmt::Assign(lhs, rhs) => self.assign_stmt(lhs, rhs),
            Stmt::Return(value) => self.return_stmt(value),
            Stmt::Expr(expr) => Ok(self.expr(expr, &stmt.span)?.0),
        }
    }

    /// Lower an AST let statement to its IR representation.
    fn let_stmt(
        &mut self,
        mutable: bool,
        name: &'m Spanned<String>,
        ty: &Option<Spanned<ast::Type>>,
        value: &'m Option<Spanned<Expr>>,
    ) -> Result<ir::Block> {
        let ir_type = if let Some(ty) = &ty {
            Some(self.ty(ty)?)
        } else {
            None
        };

        let (instrs, op_ty) = if let Some(expr) = value {
            let (mut i, o, t) = self.expr(&expr.item, &expr.span)?;
            i.push(Instruction::Value(
                Spanned::new(Place::Local(self.locals.len()), name.span.clone()),
                o,
            ));
            (i, Some(t))
        } else {
            (Vec::new(), None)
        };

        match ir_type.map_or_else(
            || op_ty.ok_or_else(|| vec![Error::UndefinedType(name.clone())]),
            Ok,
        ) {
            Ok(ty) => {
                self.locals.push(Local {
                    mutable,
                    ty: ty.clone(),
                });
                self.local_ids.insert(&name.item, self.locals.len() - 1);
                Ok(instrs)
            }
            // If the let statement neither contains a type annotation nor a default value, we have
            // an error.
            Err(errors) => Err(errors),
        }
    }

    /// Lower an AST assignment statement to its IR representation.
    fn assign_stmt(&mut self, lhs: &'m Spanned<Expr>, rhs: &'m Spanned<Expr>) -> Result<ir::Block> {
        let (mut instrs, r_op, _) = self.expr(&rhs.item, &rhs.span)?;
        let (l_instrs, l_op, _) = self.expr(&lhs.item, &lhs.span)?;
        match l_op.item {
            Operand::Place(Place::Local(id)) => {
                println!("Its ok");
                instrs.extend(l_instrs);
                instrs.push(Instruction::Value(
                    Spanned::new(Place::Local(id), lhs.span.clone()),
                    r_op,
                ));
                Ok(instrs)
            }
            _ => Err(vec![Error::UnassignableExpr(lhs.span.clone())]),
        }
    }

    /// Lower an AST return statement to its IR representation.
    fn return_stmt(&mut self, value: &'m Spanned<Expr>) -> Result<ir::Block> {
        let (mut instrs, op, _) = self.expr(&value.item, &value.span)?;
        instrs.push(Instruction::Value(
            Spanned::new(Place::Local(0), value.span.clone()),
            op,
        ));
        instrs.push(Instruction::Return);
        Ok(instrs)
    }

    /// Lower an AST expression to its IR representation and type.
    fn expr(
        &mut self,
        expr: &'m Expr,
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        match &expr {
            Expr::If(cond, then, els) => self.if_expr(cond, then, els, span),
            Expr::Call(callee, args) => self.call_expr(callee, args, span),
            Expr::Borrow(mutable, place) => self.borrow_expr(*mutable, place, span),
            Expr::Field(place, index) => self.field_expr(place, index, span),
            Expr::Deref(place) => self.deref_expr(place, span),
            Expr::Tuple(elems) => self.tuple_expr(elems, span),
            Expr::Block(block) => self.block_expr(block),
            Expr::Name(name) => {
                let (op, ty) = self.name_expr(name, span)?;
                Ok((Vec::new(), op, ty))
            }
            Expr::Int(value) => Ok((
                Vec::new(),
                Spanned::new(Operand::Int(*value), span.clone()),
                Spanned::new(ir::Type::I32, span.clone()),
            )),
            Expr::Bool(value) => Ok((
                Vec::new(),
                Spanned::new(Operand::Bool(*value), span.clone()),
                Spanned::new(ir::Type::Bool, span.clone()),
            )),
        }
    }

    /// Lower an AST if expression to its IR representation and type.
    fn if_expr(
        &mut self,
        cond: &'m Spanned<Expr>,
        then: &'m Spanned<ast::Block>,
        els: &'m Spanned<Expr>,
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let (mut instrs, cond_op, _) = self.expr(&cond.item, &cond.span)?;
        let (mut then_instrs, then_op, then_ty) = self.block_expr(&then.item)?;
        let (mut els_instrs, els_op, _) = self.expr(&els.item, &els.span)?;

        self.locals.push(Local {
            mutable: true,
            ty: then_ty.clone(),
        });
        let target = Spanned::new(Place::Local(self.locals.len() - 1), span.clone());
        then_instrs.push(Instruction::Value(target.clone(), then_op));
        els_instrs.push(Instruction::Value(target.clone(), els_op));
        instrs.push(Instruction::If(cond_op, then_instrs, els_instrs));
        Ok((
            instrs,
            Spanned::new(Operand::Place(target.item), target.span),
            Spanned::new(then_ty.item, span.clone()),
        ))
    }

    /// Lower an AST call expression to its IR representation and type.
    fn call_expr(
        &mut self,
        callee: &'m Spanned<Expr>,
        args: &'m [Spanned<Expr>],
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let (mut instrs, operand, ty) = self.expr(&callee.item, &callee.span)?;
        let (place_instrs, place) = self.as_place(operand, &ty);
        instrs.extend(place_instrs);

        let mut operands = Vec::new();
        for arg in args {
            match self.expr(&arg.item, &arg.span) {
                Ok((i, o, _)) => {
                    instrs.extend(i);
                    operands.push(o);
                }
                Err(errors) => return Err(errors),
            }
        }

        let ty = match ty.item {
            ir::Type::Fn(_, result) => *result,
            _ => return Err(vec![Error::InvalidCallee(callee.span.clone())]),
        };
        self.locals.push(Local {
            mutable: true,
            ty: ty.clone(),
        });
        let target = Spanned::new(Place::Local(self.locals.len() - 1), span.clone());
        instrs.push(Instruction::Call(target.clone(), place, operands));

        Ok((
            instrs,
            Spanned::new(Operand::Place(target.item), target.span),
            ty,
        ))
    }

    /// Lower an AST borrow expression to its IR representation and type.
    fn borrow_expr(
        &mut self,
        mutable: bool,
        expr: &'m Spanned<Expr>,
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let (mut instrs, operand, ty) = self.expr(&expr.item, &expr.span)?;
        let (place_instrs, place) = self.as_place(operand, &ty);
        instrs.extend(place_instrs);
        self.locals.push(Local {
            mutable: true,
            ty: ty.clone(),
        });
        let target = Spanned::new(Place::Local(self.locals.len() - 1), span.clone());
        instrs.push(Instruction::Borrow(target.clone(), mutable, place));
        Ok((
            instrs,
            Spanned::new(Operand::Place(target.item), target.span),
            Spanned::new(ir::Type::Ref(None, mutable, Box::new(ty)), span.clone()),
        ))
    }

    /// Lower an AST field expression to its IR representation and type.
    fn field_expr(
        &mut self,
        expr: &'m Spanned<Expr>,
        index: &Spanned<usize>,
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let (instrs, operand, ty) = self.expr(&expr.item, &expr.span)?;
        match (operand.item, ty.item) {
            (Operand::Place(p), ir::Type::Tuple(tys)) => {
                if index.item < tys.len() {
                    Ok((
                        instrs,
                        Spanned::new(
                            Operand::Place(Place::Field(
                                Box::new(Spanned::new(p, expr.span.clone())),
                                index.clone(),
                            )),
                            span.clone(),
                        ),
                        tys[index.item].clone(),
                    ))
                } else {
                    Err(vec![Error::InvalidField(span.clone(), index.clone())])
                }
            }
            _ => Err(vec![Error::InvalidField(span.clone(), index.clone())]),
        }
    }

    /// Lower an AST dereference expression to its IR representation and type.
    fn deref_expr(
        &mut self,
        expr: &'m Spanned<Expr>,
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let (instrs, operand, ty) = self.expr(&expr.item, &expr.span)?;
        match (operand.item, ty.item) {
            (Operand::Place(p), ir::Type::Ref(_, _, ty)) => Ok((
                instrs,
                Spanned::new(
                    Operand::Place(Place::Deref(Box::new(Spanned::new(p, expr.span.clone())))),
                    span.clone(),
                ),
                *ty,
            )),
            _ => Err(vec![Error::InvalidDeref(expr.span.clone())]),
        }
    }

    /// Lower an AST tuple expression to its IR representation and type.
    fn tuple_expr(
        &mut self,
        elems: &'m [Spanned<Expr>],
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let mut instrs = Vec::new();
        let mut operands = Vec::new();
        let mut tys = Vec::new();
        let mut errors = Vec::new();

        for elem in elems {
            self.expr(&elem.item, &elem.span).map_or_else(
                |errs| errors.extend(errs),
                |(i, o, t)| {
                    instrs.extend(i);
                    operands.push(o);
                    tys.push(t);
                },
            );
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok((
            instrs,
            Spanned::new(Operand::Tuple(operands), span.clone()),
            Spanned::new(ir::Type::Tuple(tys), span.clone()),
        ))
    }

    /// Lower an AST block expression to its IR representation and type.
    fn block_expr(
        &mut self,
        block: &'m ast::Block,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        self.local_ids.push_scope(true);
        let mut instrs = Vec::new();
        let mut errors = Vec::new();

        for stmt in &block.stmts {
            self.stmt(stmt)
                .map_or_else(|errs| errors.extend(errs), |i| instrs.extend(i));
        }
        if !errors.is_empty() {
            self.local_ids.pop_scope();
            return Err(errors);
        }

        let result = match self.expr(&block.result.item, &block.result.span) {
            Ok((i, o, t)) => {
                instrs.extend(i);
                Ok((instrs, o, t))
            }
            Err(errs) => Err(errs),
        };

        self.local_ids.pop_scope();
        result
    }

    /// Lower an AST name expression to its IR representation and type.
    fn name_expr(
        &self,
        name: &'m str,
        span: &Span,
    ) -> Result<(Spanned<Operand>, Spanned<ir::Type>)> {
        match self.local_ids.get(name) {
            Some(id) => Ok((
                Spanned::new(Operand::Place(Place::Local(*id)), span.clone()),
                self.locals[*id].ty.clone(),
            )),
            None => match self.globals.get(name) {
                Some(ty) => Ok((
                    Spanned::new(
                        Operand::Place(Place::Global(name.to_string())),
                        span.clone(),
                    ),
                    ty.clone(),
                )),
                None => Err(vec![Error::UndefinedName(Spanned::new(
                    name.to_string(),
                    span.clone(),
                ))]),
            },
        }
    }

    /// Transform an IR operand to a place expression.
    fn as_place(
        &mut self,
        operand: Spanned<Operand>,
        ty: &Spanned<ir::Type>,
    ) -> (ir::Block, Spanned<Place>) {
        match operand.item {
            Operand::Place(p) => (Vec::new(), Spanned::new(p, operand.span)),
            _ => {
                self.locals.push(Local {
                    mutable: true,
                    ty: ty.clone(),
                });
                let place = Spanned::new(Place::Local(self.locals.len() - 1), operand.span.clone());
                (vec![Instruction::Value(place.clone(), operand)], place)
            }
        }
    }
}
