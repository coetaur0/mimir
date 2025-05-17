//! AST to IR lowering functions.

use std::{collections::HashMap, mem, result};

use crate::{
    ast::{self, Expr, Parameter, Stmt},
    ir::{self, Instruction, Local, LocalId, Operand, OriginId, Place},
    source::{Span, Spanned},
};

/// Lower an AST module to its IR representation.
pub fn lower(module: &ast::Module) -> Result<ir::Module> {
    let mut lowerer = Lowerer {
        globals: HashMap::new(),
        origin_ids: HashMap::new(),
        local_ids: SymbolTable::new(),
        locals: Vec::new(),
    };
    let mut errors = Vec::new();

    lowerer
        .globals(module)
        .unwrap_or_else(|errs| errors.extend(errs));

    match lowerer.module(module) {
        Ok(module) => {
            if !errors.is_empty() {
                return Err(errors);
            }
            Ok(module)
        }
        Err(errs) => {
            errors.extend(errs);
            Err(errors)
        }
    }
}

/// An AST lowering result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// An AST lowering error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    DuplicateOrigin(Spanned<String>),
    UndefinedOrigin(Spanned<String>),
    DuplicateParameter(Spanned<String>),
    UndefinedType(Spanned<String>),
    UndefinedGlobal(Spanned<String>),
    InvalidCallee(Span),
    InvalidIndex(Span),
    InvalidDeref(Span),
    UnassignableExpr(Span),
    UndefinedVariable(Spanned<String>),
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
                if self.origin_ids.insert(&o.item, i).is_some() {
                    errors.push(Error::DuplicateOrigin(o.clone()));
                };
                o.item.clone()
            })
            .collect();

        // Lower the function's return type.
        self.locals.push(ir::Local {
            mutable: true,
            name: None,
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
            let (mut instrs, op) = self.block(&function.body)?;
            let span = op.span.clone();
            // Assign the body's result to the function's return local in the IR.
            instrs.push(Instruction::Value(
                Spanned::new(Place::Local(0), span.clone()),
                op,
            ));
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
            name: Some(param.name.item.clone()),
            ty,
        })
    }

    /// Lower an AST type to its IR representation.
    fn ty(&self, ty: &Spanned<ast::Type>) -> Result<Spanned<ir::Type>> {
        match &ty.item {
            ast::Type::Fn(params, result) => self.fn_ty(params, result, &ty.span),
            ast::Type::Ref(origin, mutable, r) => self.ref_ty(origin, *mutable, r, &ty.span),
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

    /// Lower an AST block expression to its corresponding IR instructions and operand.
    fn block(&mut self, block: &'m ast::Block) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        self.local_ids.push_scope(true);
        let mut instrs = Vec::new();
        let mut errors = Vec::new();

        for stmt in &block.stmts {
            self.stmt(stmt)
                .map_or_else(|errs| errors.extend(errs), |i| instrs.extend(i));
        }

        let result = match self.expr(&block.result.item, &block.result.span) {
            Ok((i, o)) => {
                instrs.extend(i);
                Ok((instrs, o))
            }
            Err(errs) => {
                errors.extend(errs);
                Err(errors)
            }
        };

        self.local_ids.pop_scope();
        result
    }

    /// Lower an AST statement to a sequence of IR instructions.
    fn stmt(&mut self, stmt: &'m Spanned<Stmt>) -> Result<Vec<Instruction>> {
        match &stmt.item {
            Stmt::Let(mutable, name, ty, value) => self.let_stmt(*mutable, name, ty, value),
            Stmt::Assign(lhs, rhs) => self.assign_stmt(lhs, rhs),
            Stmt::Return(value) => self.return_stmt(value),
            Stmt::Expr(expr) => Ok(self.expr(expr, &stmt.span)?.0),
        }
    }

    /// Lower a let statement to a sequence of IR instructions.
    fn let_stmt(
        &mut self,
        mutable: bool,
        name: &'m Spanned<String>,
        ty: &Option<Spanned<ast::Type>>,
        value: &'m Option<Spanned<Expr>>,
    ) -> Result<Vec<Instruction>> {
        let ir_type = if let Some(ty) = &ty {
            Some(self.ty(ty)?)
        } else {
            None
        };

        let (instrs, operand) = if let Some(expr) = value {
            let (mut i, o) = self.expr(&expr.item, &expr.span)?;
            i.push(Instruction::Value(
                Spanned::new(Place::Local(self.locals.len()), expr.span.clone()),
                o.clone(),
            ));
            (i, Some(o))
        } else {
            (Vec::new(), None)
        };

        match ir_type.map_or_else(
            || {
                operand.map_or(Err(vec![Error::UndefinedType(name.clone())]), |o| {
                    self.operand_ty(&o)
                })
            },
            Ok,
        ) {
            Ok(ty) => {
                self.add_local(mutable, Some(&name.item), ty);
                Ok(instrs)
            }
            // If the let statement neither contains a type annotation nor a default value, we have
            // an error.
            Err(errors) => Err(errors),
        }
    }

    /// Lower an assignment statement to a sequence of IR instructions.
    fn assign_stmt(
        &mut self,
        lhs: &'m Spanned<Expr>,
        rhs: &'m Spanned<Expr>,
    ) -> Result<Vec<Instruction>> {
        let (mut instrs, r_operand) = self.expr(&rhs.item, &rhs.span)?;
        let (l_instrs, l_operand) = self.expr(&lhs.item, &lhs.span)?;
        match l_operand.item {
            Operand::Place(p) => match p {
                Place::Global(_) => Err(vec![Error::UnassignableExpr(lhs.span.clone())]),
                _ => {
                    instrs.extend(l_instrs);
                    instrs.push(Instruction::Value(
                        Spanned::new(p, lhs.span.clone()),
                        r_operand,
                    ));
                    Ok(instrs)
                }
            },
            _ => Err(vec![Error::UnassignableExpr(lhs.span.clone())]),
        }
    }

    /// Lower a return statement to a sequence of IR instructions.
    fn return_stmt(&mut self, value: &'m Spanned<Expr>) -> Result<Vec<Instruction>> {
        let (mut instrs, operand) = self.expr(&value.item, &value.span)?;
        instrs.push(Instruction::Value(
            Spanned::new(Place::Local(0), value.span.clone()),
            operand,
        ));
        instrs.push(Instruction::Return);
        Ok(instrs)
    }

    /// Lower an AST expression to a sequence of IR instructions and an operand representing its
    /// value.
    fn expr(
        &mut self,
        expr: &'m Expr,
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        match &expr {
            Expr::If(cond, then, els) => self.if_expr(cond, then, els),
            Expr::Call(callee, args) => self.call_expr(callee, args, span),
            Expr::Borrow(mutable, e) => self.borrow_expr(*mutable, e, span),
            Expr::Field(e, index) => self.field_expr(e, index, span),
            Expr::Deref(e) => self.deref_expr(e, span),
            Expr::Tuple(elems) => self.tuple_expr(elems, span),
            Expr::Block(block) => self.block(block),
            Expr::Name(name) => self.name_expr(name, span),
            Expr::Int(value) => Ok((Vec::new(), Spanned::new(Operand::Int(*value), span.clone()))),
            Expr::Bool(value) => Ok((
                Vec::new(),
                Spanned::new(Operand::Bool(*value), span.clone()),
            )),
        }
    }

    /// Lower a conditional expression to a sequence of IR instructions and an operand.
    fn if_expr(
        &mut self,
        cond: &'m Spanned<Expr>,
        then: &'m Spanned<ast::Block>,
        els: &'m Spanned<Expr>,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        todo!()
    }

    /// Lower a call expression to a sequence of IR instructions and an operand.
    fn call_expr(
        &mut self,
        callee: &'m Spanned<Expr>,
        args: &'m [Spanned<Expr>],
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        let (mut instrs, place, ty) = self.place_expr(callee)?;

        let mut arg_ops = Vec::new();
        for arg in args {
            match self.expr(&arg.item, &arg.span) {
                Ok((i, o)) => {
                    instrs.extend(i);
                    arg_ops.push(o);
                }
                Err(errors) => return Err(errors),
            }
        }

        let ty = match &ty.item {
            ir::Type::Fn(_, result) => *result.clone(),
            _ => return Err(vec![Error::InvalidCallee(callee.span.clone())]),
        };
        self.locals.push(Local {
            mutable: true,
            name: None,
            ty,
        });
        instrs.push(Instruction::Call(
            Spanned::new(Place::Local(self.locals.len() - 1), span.clone()),
            place,
            arg_ops,
        ));
        Ok((
            instrs,
            Spanned::new(
                Operand::Place(Place::Local(self.locals.len() - 1)),
                span.clone(),
            ),
        ))
    }

    /// Lower a borrow expression to a sequence of IR instructions and an operand.
    fn borrow_expr(
        &mut self,
        mutable: bool,
        expr: &'m Spanned<Expr>,
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        let (mut instrs, place, ty) = self.place_expr(expr)?;
        self.locals.push(Local {
            mutable: true,
            name: None,
            ty: Spanned::new(
                ir::Type::Ref(None, mutable, Box::new(ty)),
                place.span.clone(),
            ),
        });
        instrs.push(Instruction::Borrow(
            Spanned::new(Place::Local(self.locals.len() - 1), span.clone()),
            mutable,
            place,
        ));
        Ok((
            instrs,
            Spanned::new(
                Operand::Place(Place::Local(self.locals.len())),
                span.clone(),
            ),
        ))
    }

    /// Lower a field index expression to a sequence of IR instructions and an operand.
    fn field_expr(
        &mut self,
        expr: &'m Spanned<Expr>,
        index: &Spanned<usize>,
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        let (instrs, operand) = self.expr(&expr.item, &expr.span)?;
        match operand.item {
            Operand::Place(p) => Ok((
                instrs,
                Spanned::new(
                    Operand::Place(Place::Field(
                        Box::new(Spanned::new(p, expr.span.clone())),
                        index.clone(),
                    )),
                    span.clone(),
                ),
            )),
            _ => Err(vec![Error::InvalidIndex(span.clone())]),
        }
    }

    /// Lower a dereference expression to a sequence of IR instructions and an operand.
    fn deref_expr(
        &mut self,
        expr: &'m Spanned<Expr>,
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        let (instrs, operand) = self.expr(&expr.item, &expr.span)?;
        match operand.item {
            Operand::Place(p) => Ok((
                instrs,
                Spanned::new(
                    Operand::Place(Place::Deref(Box::new(Spanned::new(p, expr.span.clone())))),
                    span.clone(),
                ),
            )),
            _ => Err(vec![Error::InvalidDeref(expr.span.clone())]),
        }
    }

    /// Lower a tuple expression to a sequence of IR instructions and an operand.
    fn tuple_expr(
        &mut self,
        elems: &'m [Spanned<Expr>],
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        let mut instrs = Vec::new();
        let mut operands = Vec::new();
        let mut errors = Vec::new();

        for elem in elems {
            self.expr(&elem.item, &elem.span).map_or_else(
                |errs| errors.extend(errs),
                |(i, o)| {
                    instrs.extend(i);
                    operands.push(o);
                },
            );
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok((instrs, Spanned::new(Operand::Tuple(operands), span.clone())))
    }

    /// Lower a name expression to a sequence of IR instructions and an operand.
    fn name_expr(
        &mut self,
        name: &'m str,
        span: &Span,
    ) -> Result<(Vec<Instruction>, Spanned<Operand>)> {
        match self.local_ids.get(name) {
            Some(id) => Ok((
                Vec::new(),
                Spanned::new(Operand::Place(Place::Local(*id)), span.clone()),
            )),
            None => Err(vec![Error::UndefinedVariable(Spanned::new(
                name.to_string(),
                span.clone(),
            ))]),
        }
    }

    /// Lower an expression to a sequence of instructions and a place.
    fn place_expr(
        &mut self,
        expr: &'m Spanned<Expr>,
    ) -> Result<(Vec<Instruction>, Spanned<Place>, Spanned<ir::Type>)> {
        let (mut instrs, operand) = self.expr(&expr.item, &expr.span)?;
        let ty = self.operand_ty(&operand)?;
        let place = match operand.item {
            Operand::Place(p) => Spanned::new(p, operand.span),
            _ => {
                let span = operand.span.clone();
                instrs.push(Instruction::Value(
                    Spanned::new(Place::Local(self.locals.len()), span.clone()),
                    operand,
                ));
                self.locals.push(Local {
                    mutable: true,
                    name: None,
                    ty: ty.clone(),
                });
                Spanned::new(Place::Local(self.locals.len() - 1), span)
            }
        };
        Ok((instrs, place, ty))
    }

    /// Get the IR type of an operand.
    fn operand_ty(&self, operand: &Spanned<Operand>) -> Result<Spanned<ir::Type>> {
        match &operand.item {
            Operand::Tuple(elems) => {
                let mut tys = Vec::new();
                for op in elems {
                    tys.push(self.operand_ty(op)?);
                }
                Ok(Spanned::new(ir::Type::Tuple(tys), operand.span.clone()))
            }
            Operand::Place(place) => self.place_ty(place, &operand.span),
            Operand::Int(_) => Ok(Spanned::new(ir::Type::I32, operand.span.clone())),
            Operand::Bool(_) => Ok(Spanned::new(ir::Type::Bool, operand.span.clone())),
        }
    }

    /// Get the IR type of a place expression.
    fn place_ty(&self, place: &Place, span: &Span) -> Result<Spanned<ir::Type>> {
        match &place {
            Place::Field(place, index) => match self.place_ty(&place.item, &place.span) {
                Ok(Spanned {
                    item: ir::Type::Tuple(tys),
                    span: _,
                }) if index.item < tys.len() => Ok(tys[index.item].clone()),
                Ok(_) => Err(vec![Error::InvalidIndex(span.clone())]),
                Err(errors) => Err(errors),
            },
            Place::Deref(place) => match self.place_ty(&place.item, &place.span) {
                Ok(Spanned {
                    item: ir::Type::Ref(_, _, ty),
                    span: _,
                }) => Ok(*ty.clone()),
                Ok(_) => Err(vec![Error::InvalidDeref(span.clone())]),
                Err(errors) => Err(errors),
            },
            Place::Global(name) => match self.globals.get(name.as_str()) {
                Some(ty) => Ok(ty.clone()),
                None => Err(vec![Error::UndefinedGlobal(Spanned::new(
                    name.to_string(),
                    span.clone(),
                ))]),
            },
            Place::Local(id) => Ok(self.locals[*id].ty.clone()),
        }
    }

    /// Create a new local with a given mutability, name and type.
    fn add_local(&mut self, mutable: bool, name: Option<&'m str>, ty: Spanned<ir::Type>) {
        let name = if let Some(name) = name {
            self.local_ids.insert(&name, self.locals.len());
            Some(name.to_string())
        } else {
            None
        };
        self.locals.push(Local { mutable, name, ty });
    }
}

/// A symbol table mapping names to values inside a hierarchy of scopes.
struct SymbolTable<'m, T> {
    scopes: Vec<Scope<'m, T>>,
}

impl<'m, T> SymbolTable<'m, T> {
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
    pub fn insert(&mut self, name: &'m str, value: T) -> bool {
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
struct Scope<'m, T> {
    bindings: HashMap<&'m str, T>,
    shadowing: bool,
}

impl<'m, T> Scope<'m, T> {
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
    pub fn insert(&mut self, name: &'m str, value: T) -> bool {
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
