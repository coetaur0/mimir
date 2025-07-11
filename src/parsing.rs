//! Parsing module.

use std::{collections::HashMap, fmt};

use logos::{Lexer, Logos};

use crate::{
    ast::*,
    reporting::{Error, Result, Span, Spanned},
};

/// Parse a Mim module.
pub fn parse(src: &str) -> Result<Module> {
    let mut parser = Parser::new(src);
    parser.module()
}

/// A lexical token.
#[derive(Clone, Copy, Debug, Eq, Logos, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
pub enum Token {
    // Keywords:
    #[token("fn")]
    FnKw,
    #[token("i32")]
    I32Kw,
    #[token("bool")]
    BoolKw,
    #[token("mut")]
    MutKw,
    #[token("while")]
    WhileKw,
    #[token("let")]
    LetKw,
    #[token("return")]
    ReturnKw,
    #[token("if")]
    IfKw,
    #[token("else")]
    ElseKw,

    // Literals:
    #[regex(r"'(\p{XID_Start}|_)\p{XID_Continue}*", priority = 1)]
    Origin,
    #[token("'_", priority = 2)]
    LocalOrigin,
    #[regex(r"(\p{XID_Start}|_)\p{XID_Continue}*")]
    Name,
    #[regex(r"[0-9][_0-9]*")]
    IntLit,
    #[token("true")]
    TrueLit,
    #[token("false")]
    FalseLit,

    // Punctuation:
    #[token("<")]
    LAngle,
    #[token(">")]
    RAngle,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("->")]
    Arrow,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token("=")]
    Assign,
    #[token("&")]
    Ampersand,
    #[token("*")]
    Star,
    Eof,

    // Errors:
    Unknown,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::FnKw => write!(f, "the 'fn' keyword"),
            Token::I32Kw => write!(f, "the 'i32' keyword"),
            Token::BoolKw => write!(f, "the 'bool' keyword"),
            Token::MutKw => write!(f, "the 'mut' keyword"),
            Token::WhileKw => write!(f, "the 'while' keyword"),
            Token::LetKw => write!(f, "the 'let' keyword"),
            Token::ReturnKw => write!(f, "the 'return' keyword"),
            Token::IfKw => write!(f, "the 'if' keyword"),
            Token::ElseKw => write!(f, "the 'else' keyword"),
            Token::Origin => write!(f, "an origin"),
            Token::LocalOrigin => write!(f, "the local origin"),
            Token::Name => write!(f, "a name"),
            Token::IntLit => write!(f, "an integer literal"),
            Token::TrueLit => write!(f, "the 'true' boolean literal"),
            Token::FalseLit => write!(f, "the 'false' boolean literal"),
            Token::LAngle => write!(f, "a '<'"),
            Token::RAngle => write!(f, "a '>'"),
            Token::LParen => write!(f, "a '('"),
            Token::RParen => write!(f, "a ')'"),
            Token::LBrace => write!(f, "a '{{'"),
            Token::RBrace => write!(f, "a '}}'"),
            Token::Arrow => write!(f, "a '->'"),
            Token::Comma => write!(f, "a ','"),
            Token::Colon => write!(f, "a ':'"),
            Token::Semicolon => write!(f, "a ';'"),
            Token::Assign => write!(f, "a '='"),
            Token::Ampersand => write!(f, "a '&'"),
            Token::Star => write!(f, "a '*'"),
            Token::Eof => write!(f, "the end of file"),
            Token::Unknown => write!(f, "an unknown symbol"),
        }
    }
}

/// A parser for Mim.
struct Parser<'src> {
    lexer: Lexer<'src, Token>,
    token: Token,
}

impl<'src> Parser<'src> {
    /// Create a new parser for some source string.
    fn new(src: &'src str) -> Self {
        let mut lexer = Token::lexer(src);
        let token = lexer
            .next()
            .map(|tok| tok.unwrap_or(Token::Unknown))
            .unwrap_or(Token::Eof);
        Parser { lexer, token }
    }

    /// Parse a module declaration.
    fn module(&mut self) -> Result<Module> {
        let mut functions = HashMap::new();
        let mut errors = Vec::new();

        while self.token != Token::Eof {
            match self.function() {
                Ok((name, decl)) => {
                    if functions.insert(name.item.clone(), decl).is_some() {
                        errors.push(Error::DuplicateFunction(name));
                    }
                }
                Err(errs) => {
                    errors.extend(errs);
                    self.recover(&[Token::FnKw]);
                }
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(Module { functions })
    }

    /// Parse a function declaration.
    fn function(&mut self) -> Result<(Spanned<String>, Function)> {
        self.expect(Token::FnKw)?;
        let name = self.expect(Token::Name)?;
        let origins = self.optional(
            |p| {
                p.delimited(
                    |p| p.list(|p| p.expect(Token::Origin), Token::Comma, Token::RAngle),
                    Token::LAngle,
                    Token::RAngle,
                )
                .map(|r| r.item)
            },
            Token::LAngle,
            Vec::new(),
        )?;
        let params = self
            .delimited(
                |p| p.list(Self::parameter, Token::Comma, Token::RParen),
                Token::LParen,
                Token::RParen,
            )?
            .item;
        let result = if self.peek(Token::Arrow) {
            self.advance();
            self.ty()?
        } else {
            Spanned::new(Type::Unit, self.span())
        };
        let body = self.block()?.item;
        Ok((
            name,
            Function {
                origins,
                params,
                result,
                body,
            },
        ))
    }

    /// Parse a function parameter.
    fn parameter(&mut self) -> Result<Parameter> {
        let mutable = self.mutable()?;
        let name = self.expect(Token::Name)?;
        self.expect(Token::Colon)?;
        let ty = self.ty()?;
        Ok(Parameter { mutable, name, ty })
    }

    /// Parse a block expression.
    fn block(&mut self) -> Result<Spanned<Block>> {
        let open = self.expect(Token::LBrace)?;
        let mut stmts = Vec::new();
        let mut result = None;
        let mut errors = Vec::new();

        while self.token != Token::Eof && !self.peek(Token::RBrace) {
            match self.stmt() {
                Ok(stmt) => match stmt.item {
                    Stmt::Expr(expr) if self.peek(Token::RBrace) => {
                        result = Some(Spanned::new(expr, stmt.span));
                        break;
                    }
                    _ => stmts.push(stmt),
                },
                Err(errs) => {
                    errors.extend(errs);
                    self.recover(&[Token::Semicolon, Token::RBrace]);
                }
            }
            if self.peek(Token::Semicolon) {
                self.advance();
            } else {
                break;
            }
        }

        let start = open.span.start;
        let end = if self.peek(Token::RBrace) {
            self.consume().span.end
        } else {
            errors.push(Error::UnclosedDelimiter(
                open,
                Token::RBrace.to_string(),
                Spanned::new(self.token.to_string(), self.span()),
            ));
            return Err(errors);
        };

        if !errors.is_empty() {
            return Err(errors);
        }
        let result = match result {
            Some(expr) => expr,
            None => Spanned::new(Expr::Unit, end..end),
        };
        Ok(Spanned::new(Block { stmts, result }, start..end))
    }

    /// Parse a statement.
    fn stmt(&mut self) -> Result<Spanned<Stmt>> {
        match self.token {
            Token::WhileKw => self.while_stmt(),
            Token::LetKw => self.let_stmt(),
            Token::ReturnKw => self.return_stmt(),
            _ => self.expr_stmt(),
        }
    }

    /// Parse a while statement.
    fn while_stmt(&mut self) -> Result<Spanned<Stmt>> {
        let start = self.consume().span.start;
        let cond = self.expr()?;
        let body = self.block()?;
        let span = start..body.span.end;
        Ok(Spanned::new(Stmt::While(cond, body), span))
    }

    /// Parse a let statement.
    fn let_stmt(&mut self) -> Result<Spanned<Stmt>> {
        let start = self.consume().span.start;
        let mutable = self.mutable()?;
        let name = self.expect(Token::Name)?;
        let ty = self.optional(
            |p| {
                p.advance();
                Ok(Some(p.ty()?))
            },
            Token::Colon,
            None,
        )?;
        let value = self.optional(
            |p| {
                p.advance();
                Ok(Some(p.expr()?))
            },
            Token::Assign,
            None,
        )?;
        let end = if let Some(value) = &value {
            value.span.end
        } else if let Some(ty) = &ty {
            ty.span.end
        } else {
            name.span.end
        };
        Ok(Spanned::new(
            Stmt::Let(mutable, name, ty, value),
            start..end,
        ))
    }

    /// Parse a return statement.
    fn return_stmt(&mut self) -> Result<Spanned<Stmt>> {
        let start = self.consume().span.start;
        let value = self.expr()?;
        let span = start..value.span.end;
        Ok(Spanned::new(Stmt::Return(value), span))
    }

    /// Parse an assignment or expression statement.
    fn expr_stmt(&mut self) -> Result<Spanned<Stmt>> {
        let expr = self.expr()?;
        Ok(
            match self.optional(
                |p| {
                    p.advance();
                    Ok(Some(p.expr()?))
                },
                Token::Assign,
                None,
            )? {
                Some(value) => {
                    let span = expr.span.start..value.span.end;
                    Spanned::new(Stmt::Assign(expr, value), span)
                }
                None => Spanned::new(Stmt::Expr(expr.item), expr.span),
            },
        )
    }

    /// Parse an expression.
    fn expr(&mut self) -> Result<Spanned<Expr>> {
        if self.peek(Token::Star) {
            let start = self.consume().span.start;
            let expr = self.expr()?;
            let span = start..expr.span.end;
            Ok(Spanned::new(Expr::Deref(Box::new(expr)), span))
        } else {
            self.call_expr()
        }
    }

    /// Parse an optional sequence of call expressions.
    fn call_expr(&mut self) -> Result<Spanned<Expr>> {
        let mut expr = self.primary_expr()?;
        loop {
            match self.token {
                Token::LParen => {
                    let args = self.delimited(
                        |p| p.list(Self::expr, Token::Comma, Token::RParen),
                        Token::LParen,
                        Token::RParen,
                    )?;
                    let span = expr.span.start..args.span.end;
                    expr = Spanned::new(Expr::Call(Box::new(expr), args.item), span);
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    /// Parse a primary expression.
    fn primary_expr(&mut self) -> Result<Spanned<Expr>> {
        match self.token {
            Token::IfKw => self.if_expr(),
            Token::LParen => self.paren_expr(),
            Token::Ampersand => self.borrow_expr(),
            Token::Name => self.name_expr(),
            Token::IntLit => self.int_expr(),
            Token::LBrace => {
                let block = self.block()?;
                Ok(Spanned::new(Expr::Block(Box::new(block.item)), block.span))
            }
            Token::TrueLit => {
                let span = self.consume().span;
                Ok(Spanned::new(Expr::Bool(true), span))
            }
            Token::FalseLit => {
                let span = self.consume().span;
                Ok(Spanned::new(Expr::Bool(false), span))
            }
            _ => Err(self.expected("an expression".to_string())),
        }
    }

    /// Parse a conditional expression.
    fn if_expr(&mut self) -> Result<Spanned<Expr>> {
        let start = self.consume().span.start;
        let cond = self.expr()?;
        let then = self.block()?;
        let els = if self.peek(Token::ElseKw) {
            self.advance();
            if self.peek(Token::IfKw) {
                self.if_expr()?
            } else {
                let block = self.block()?;
                Spanned::new(Expr::Block(Box::new(block.item)), block.span)
            }
        } else {
            Spanned::new(Expr::Unit, self.lexer.span())
        };
        let span = start..els.span.end;
        Ok(Spanned::new(
            Expr::If(Box::new(cond), Box::new(then), Box::new(els)),
            span,
        ))
    }

    /// Parse a parenthesized or unit expression.
    fn paren_expr(&mut self) -> Result<Spanned<Expr>> {
        let start = self.consume().span.start;
        if self.peek(Token::RParen) {
            return Ok(Spanned::new(Expr::Unit, start..self.consume().span.end));
        }
        let expr = self.expr()?;
        self.expect(Token::RParen)?;
        Ok(expr)
    }

    /// Parse a borrow expression.
    fn borrow_expr(&mut self) -> Result<Spanned<Expr>> {
        let start = self.consume().span.start;
        let mutable = self.mutable()?;
        let expr = self.expr()?;
        let span = start..expr.span.end;
        Ok(Spanned::new(Expr::Borrow(mutable, Box::new(expr)), span))
    }

    /// Parse a name expression.
    fn name_expr(&mut self) -> Result<Spanned<Expr>> {
        let name = self.expect(Token::Name)?;
        let origin_args = self.optional(
            |p| {
                p.delimited(
                    |p| p.list(Self::origin_arg, Token::Comma, Token::RAngle),
                    Token::LAngle,
                    Token::RAngle,
                )
            },
            Token::LAngle,
            Spanned::new(Vec::new(), name.span.clone()),
        )?;
        let span = name.span.start..origin_args.span.end;
        Ok(Spanned::new(Expr::Name(name, origin_args.item), span))
    }

    /// Parse an integer literal.
    fn int_expr(&mut self) -> Result<Spanned<Expr>> {
        let number = self.expect(Token::IntLit)?;
        match number.item.parse::<i32>() {
            Ok(value) => Ok(Spanned::new(Expr::Int(value), number.span)),
            Err(_) => Err(self.expected("a valid integer constant".to_string())),
        }
    }

    /// Parse an origin argument.
    fn origin_arg(&mut self) -> Result<Option<Spanned<String>>> {
        match self.token {
            Token::Origin => Ok(Some(self.expect(Token::Origin).unwrap())),
            Token::LocalOrigin => {
                self.advance();
                Ok(None)
            }
            _ => Err(self.expected("an origin argument".to_string())),
        }
    }

    /// Parse a type expression.
    fn ty(&mut self) -> Result<Spanned<Type>> {
        match self.token {
            Token::FnKw => self.fn_ty(),
            Token::Ampersand => self.ref_ty(),
            Token::LParen => self.paren_ty(),
            Token::I32Kw => {
                let span = self.consume().span;
                Ok(Spanned::new(Type::I32, span))
            }
            Token::BoolKw => {
                let span = self.consume().span;
                Ok(Spanned::new(Type::Bool, span))
            }
            _ => Err(self.expected("a type expression".to_string())),
        }
    }

    /// Parse a function type expression.
    fn fn_ty(&mut self) -> Result<Spanned<Type>> {
        let start = self.consume().span.start;
        let params = self
            .delimited(
                |p| p.list(Self::ty, Token::Comma, Token::RParen),
                Token::LParen,
                Token::RParen,
            )?
            .item;
        self.expect(Token::Arrow)?;
        let result = self.ty()?;
        let span = start..result.span.end;
        Ok(Spanned::new(Type::Fn(params, Box::new(result)), span))
    }

    /// Parse a reference type expression.
    fn ref_ty(&mut self) -> Result<Spanned<Type>> {
        let start = self.consume().span.start;
        let origin = self.optional(|p| Ok(Some(p.expect(Token::Origin)?)), Token::Origin, None)?;
        let mutable = self.mutable()?;
        let ty = self.ty()?;
        let span = start..ty.span.end;
        Ok(Spanned::new(Type::Ref(origin, mutable, Box::new(ty)), span))
    }

    /// Parse a parenthesized or unit type expression.
    fn paren_ty(&mut self) -> Result<Spanned<Type>> {
        let start = self.consume().span.start;
        if self.peek(Token::RParen) {
            return Ok(Spanned::new(Type::Unit, start..self.consume().span.end));
        }
        let ty = self.ty()?;
        self.expect(Token::RParen)?;
        Ok(ty)
    }

    /// Parse an optional mutability marker.
    fn mutable(&mut self) -> Result<bool> {
        self.optional(
            |p| {
                p.advance();
                Ok(true)
            },
            Token::MutKw,
            false,
        )
    }

    /// Parse an item delimited by a pair of `open` and `close` tokens.
    fn delimited<T, F>(&mut self, parse: F, open: Token, close: Token) -> Result<Spanned<T>>
    where
        F: Fn(&mut Self) -> Result<T>,
    {
        let open = self.expect(open)?;
        let item = parse(self)?;

        if self.peek(close) {
            let end = self.consume().span.end;
            Ok(Spanned::new(item, open.span.start..end))
        } else {
            Err(vec![Error::UnclosedDelimiter(
                open,
                close.to_string(),
                Spanned::new(self.token.to_string(), self.span()),
            )])
        }
    }

    /// Parse a list of items separated by a given token kind and ending with some `close` token.
    fn list<T, F>(&mut self, parse: F, separator: Token, close: Token) -> Result<Vec<T>>
    where
        F: Fn(&mut Self) -> Result<T>,
    {
        let mut items = Vec::new();
        let mut errors = Vec::new();

        while self.token != Token::Eof && !self.peek(close) {
            match parse(self) {
                Ok(item) => items.push(item),
                Err(errs) => {
                    errors.extend(errs);
                    self.recover(&[separator, close]);
                }
            }
            if self.peek(separator) {
                self.advance();
            } else {
                break;
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(items)
    }

    /// Parse an item starting with some `open` token and return it, or return some default value if
    /// the next token in the source doesn't match the `open` kind.
    fn optional<T, F>(&mut self, parse: F, open: Token, default: T) -> Result<T>
    where
        F: Fn(&mut Self) -> Result<T>,
    {
        if self.peek(open) {
            parse(self)
        } else {
            Ok(default)
        }
    }

    /// Advance the parser to the next token in the source.
    fn advance(&mut self) {
        self.token = self
            .lexer
            .next()
            .map(|tok| tok.unwrap_or(Token::Unknown))
            .unwrap_or(Token::Eof);
    }

    /// Peek at the next token in the source and check if it matches some expected token kind.
    fn peek(&self, expected: Token) -> bool {
        self.token == expected
    }

    /// Consume the next token in the source and return it with its span.
    fn consume(&mut self) -> Spanned<Token> {
        let token = self.token;
        let span = self.span();
        self.advance();
        Spanned::new(token, span)
    }

    /// Consume the next token in the source if it matches some expected token kind and return its
    /// text representation and its span, or return a syntax error otherwise.
    fn expect(&mut self, kind: Token) -> Result<Spanned<String>> {
        if self.peek(kind) {
            let text = self.text().to_string();
            let span = self.span();
            self.advance();
            Ok(Spanned::new(text, span))
        } else {
            Err(self.expected(kind.to_string()))
        }
    }

    /// Return a syntax error indicating that something else than the next token was expected in
    /// the source.
    fn expected(&self, message: String) -> Vec<Error> {
        vec![Error::UnexpectedSymbol(
            message,
            Spanned::new(self.token.to_string(), self.span()),
        )]
    }

    /// Recover at the next token in the source that belongs to a given list of token kinds.
    fn recover(&mut self, kinds: &[Token]) {
        while self.token != Token::Eof && !kinds.contains(&self.token) {
            self.advance();
        }
    }

    /// Get the string representation of the next token in the source.
    fn text(&self) -> &'src str {
        self.lexer.slice()
    }

    /// Get the span of the next token in the source.
    fn span(&self) -> Span {
        self.lexer.span()
    }
}
