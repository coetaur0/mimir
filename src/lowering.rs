//! AST to IR lowering functions.

use std::{collections::HashMap, result};

/// An AST lowering result.
pub type Result<T> = result::Result<T, Vec<Error>>;

/// An AST lowering error.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {}

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
    pub fn push(&mut self, shadowing: bool) {
        self.scopes.push(Scope::new(shadowing));
    }

    /// Pop the current (most nested) scope from the symbol table.
    pub fn pop(&mut self) {
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
