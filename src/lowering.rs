//! AST to IR lowering module.

use std::{collections::HashMap, mem};

use crate::{
    ast::{self, Expr, Parameter, Stmt},
    ir::{self, Instruction, Local, LocalId, Operand, OriginId, Place},
    reporting::{Error, Result, Span, Spanned},
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

        for (i, origin) in function.origins.iter().enumerate() {
            self.origin_ids.insert(&origin.item, i);
        }

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
            instrs.push(Instruction::Assign(Spanned::new(Place::Local(0), span), op));
            Ok(ir::Function {
                origin_count: self.origin_ids.len(),
                param_count: function.params.len(),
                locals: mem::take(&mut self.locals),
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
                .map_or(Err(vec![Error::UndefinedOrigin(name.span.clone())]), |id| {
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
            Stmt::While(cond, body) => self.while_stmt(cond, &body.item),
            Stmt::Let(mutable, name, ty, value) => self.let_stmt(*mutable, name, ty, value),
            Stmt::Assign(lhs, rhs) => self.assign_stmt(lhs, rhs),
            Stmt::Return(value) => self.return_stmt(value),
            Stmt::Expr(expr) => Ok(self.expr(expr, &stmt.span)?.0),
        }
    }

    /// Lower an AST while statement to its IR representation.
    fn while_stmt(&mut self, cond: &'m Spanned<Expr>, body: &'m ast::Block) -> Result<ir::Block> {
        let (mut instrs, cond_op, _) = self.expr(&cond.item, &cond.span)?;
        let (body_instrs, _, _) = self.block_expr(body)?;
        instrs.push(Instruction::While(cond_op, body_instrs));
        Ok(instrs)
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
            i.push(Instruction::Assign(
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
            Operand::Place(p) => {
                instrs.extend(l_instrs);
                instrs.push(Instruction::Assign(Spanned::new(p, lhs.span.clone()), r_op));
                Ok(instrs)
            }
            _ => Err(vec![Error::UnassignableExpr(lhs.span.clone())]),
        }
    }

    /// Lower an AST return statement to its IR representation.
    fn return_stmt(&mut self, value: &'m Spanned<Expr>) -> Result<ir::Block> {
        let (mut instrs, op, _) = self.expr(&value.item, &value.span)?;
        instrs.push(Instruction::Assign(
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
            Expr::Name(name, origin_args) => {
                let (op, ty) = self.name_expr(name, origin_args, span)?;
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
        then_instrs.push(Instruction::Assign(target.clone(), then_op));
        els_instrs.push(Instruction::Assign(target.clone(), els_op));
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

        let (place_instrs, place) = self.as_place(operand, &ty);
        instrs.extend(place_instrs);

        let ty = match ty.item {
            ir::Type::Fn(_, result) => *result,
            _ => return Err(vec![Error::InvalidCallee(ty.clone())]),
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
        let target_ty = Spanned::new(
            ir::Type::Ref(None, mutable, Box::new(ty.clone())),
            span.clone(),
        );
        self.locals.push(Local {
            mutable: true,
            ty: target_ty.clone(),
        });
        let target = Spanned::new(Place::Local(self.locals.len() - 1), span.clone());
        instrs.push(Instruction::Borrow(target.clone(), mutable, place));
        Ok((
            instrs,
            Spanned::new(Operand::Place(target.item), target.span),
            target_ty,
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
        match (operand.item, &ty.item) {
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
                    Err(vec![Error::InvalidField(ty.clone(), index.clone())])
                }
            }
            _ => Err(vec![Error::InvalidField(ty.clone(), index.clone())]),
        }
    }

    /// Lower an AST dereference expression to its IR representation and type.
    fn deref_expr(
        &mut self,
        expr: &'m Spanned<Expr>,
        span: &Span,
    ) -> Result<(ir::Block, Spanned<Operand>, Spanned<ir::Type>)> {
        let (instrs, operand, ty) = self.expr(&expr.item, &expr.span)?;
        match (operand.item, &ty.item) {
            (Operand::Place(p), ir::Type::Ref(_, _, ty)) => Ok((
                instrs,
                Spanned::new(
                    Operand::Place(Place::Deref(Box::new(Spanned::new(p, expr.span.clone())))),
                    span.clone(),
                ),
                *ty.clone(),
            )),
            _ => Err(vec![Error::InvalidDeref(ty.clone())]),
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
        name: &'m Spanned<String>,
        origin_args: &'m Vec<Option<Spanned<String>>>,
        span: &Span,
    ) -> Result<(Spanned<Operand>, Spanned<ir::Type>)> {
        match self.local_ids.get(&name.item) {
            Some(id) => Ok((
                Spanned::new(Operand::Place(Place::Local(*id)), name.span.clone()),
                self.locals[*id].ty.clone(),
            )),
            None => match self.globals.get::<str>(name.item.as_ref()) {
                Some(ty) => {
                    let args = self.origin_args(origin_args)?;
                    let ty_instance = ty.substitute(&args);
                    Ok((
                        Spanned::new(
                            Operand::Place(Place::Global(name.clone(), args)),
                            span.clone(),
                        ),
                        ty_instance,
                    ))
                }
                None => Err(vec![Error::UndefinedName(name.clone())]),
            },
        }
    }

    /// Lower a sequence of origin arguments to origin ids.
    fn origin_args(&self, args: &'m Vec<Option<Spanned<String>>>) -> Result<Vec<Option<OriginId>>> {
        let mut origin_ids = Vec::new();
        let mut errors = Vec::new();

        for arg in args {
            match arg {
                Some(name) => match self.origin_ids.get::<str>(name.item.as_ref()) {
                    Some(id) => origin_ids.push(Some(*id)),
                    None => errors.push(Error::UndefinedOrigin(name.span.clone())),
                },
                None => origin_ids.push(None),
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(origin_ids)
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
                (vec![Instruction::Assign(place.clone(), operand)], place)
            }
        }
    }
}

/// A symbol table mapping names to values inside a hierarchy of scopes.
struct SymbolTable<'src, T> {
    scopes: Vec<Scope<'src, T>>,
}

impl<'src, T> SymbolTable<'src, T> {
    /// Create a new symbol table.
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::new(false)],
        }
    }

    /// Clear the contents of the symbol table.
    pub fn clear(&mut self) {
        self.scopes.truncate(1);
        self.scopes[0].clear();
    }

    /// Push a new nested scope into the symbol table with shadowing allowed or not.
    pub fn push_scope(&mut self, shadowing: bool) {
        self.scopes.push(Scope::new(shadowing));
    }

    /// Pop the current (most nested) scope from the symbol table.
    pub fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Insert a new binding in the symbol table's current scope and return `true` if the insertion
    /// succeeded, or `false` if it failed.
    /// An insertion can fail if the current scope does not allow shadowing and a binding already
    /// exists with the name passed as argument.
    pub fn insert(&mut self, name: &'src str, value: T) -> bool {
        match self.scopes.last_mut() {
            Some(scope) => scope.insert(name, value),
            None => false,
        }
    }

    /// Get the value associated with some name in the symbol table, or return `None` if it is
    /// undefined.
    /// Names are searched from the most nested scope and outwards up to the table's root scope.
    pub fn get(&self, name: &str) -> Option<&T> {
        let mut i = self.scopes.len();
        while i > 0 {
            match self.scopes[i - 1].get(name) {
                Some(v) => {
                    return Some(v);
                }
                None => {
                    i -= 1;
                }
            }
        }
        None
    }
}

impl<T> Default for SymbolTable<'_, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A binding scope mapping names to values.
struct Scope<'src, T> {
    bindings: HashMap<&'src str, T>,
    shadowing: bool,
}

impl<'src, T> Scope<'src, T> {
    /// Create a new binding scope.
    pub fn new(shadowing: bool) -> Self {
        Scope {
            bindings: HashMap::new(),
            shadowing,
        }
    }

    /// Clear the contents of the scope.
    pub fn clear(&mut self) {
        self.bindings.clear();
    }

    /// Insert a new binding in the scope and return `true` if the insertion succeeded, or `false`
    /// if it failed.
    /// An insertion can fail if shadowing is disallowed and a binding with the same name is already
    /// present in the scope.
    pub fn insert(&mut self, name: &'src str, value: T) -> bool {
        if !self.shadowing && self.bindings.contains_key(name) {
            return false;
        }
        self.bindings.insert(name, value);
        true
    }

    /// Get the value associated with some name in the scope.
    pub fn get(&self, name: &str) -> Option<&T> {
        self.bindings.get(name)
    }
}
