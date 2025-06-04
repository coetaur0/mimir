//! Borrow checking module.

use std::collections::HashSet;

use crate::{
    ir::{Instruction, LocalId, Operand, Place},
    reporting::Spanned,
};

/// A path to an aliasable memory location.
/// A path corresponds to a local identifier followed by an arbitrary number of field indices.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Path {
    pub local: LocalId,
    pub fields: Vec<usize>,
}

impl From<&Place> for Option<Path> {
    /// Compute the path in a place expression, if any.
    /// Returns `None` for global places.
    fn from(value: &Place) -> Self {
        match &value {
            Place::Field(place, index) => Option::<Path>::from(&place.item).map(|mut p| {
                p.fields.push(index.item);
                p
            }),
            Place::Deref(place) => Option::<Path>::from(&place.item),
            Place::Global(_, _) => None,
            Place::Local(id) => Some(Path {
                local: *id,
                fields: Vec::new(),
            }),
        }
    }
}

impl From<&Operand> for HashSet<Path> {
    /// Compute the set of paths that appear in an instruction operand.
    fn from(value: &Operand) -> Self {
        match &value {
            Operand::Tuple(elems) => elems.iter().fold(HashSet::new(), |mut result, operand| {
                result.extend(HashSet::<Path>::from(&operand.item));
                result
            }),
            Operand::Place(place) => {
                Option::<Path>::from(place).map_or(HashSet::new(), |p| HashSet::from([p]))
            }
            Operand::Int(_) | Operand::Bool(_) => HashSet::new(),
        }
    }
}

/// Compute the sets of live-before paths for a function body.
pub fn live(instrs: &[Instruction]) -> Vec<HashSet<Path>> {
    let after = HashSet::from([Path {
        local: 0,
        fields: Vec::new(),
    }]);
    live_instrs(after, instrs.iter().rev())
}

/// Compute the sets of live-before paths for a sequence of instructions.
fn live_instrs<'i, I>(mut after: HashSet<Path>, instrs: I) -> Vec<HashSet<Path>>
where
    I: Iterator<Item = &'i Instruction>,
{
    let mut sets = Vec::new();
    for instr in instrs {
        match instr {
            Instruction::While(cond, body) => {
                let body_sets = live_while(after, cond, body);
                after = body_sets.last().unwrap().clone();
                sets.extend(body_sets);
            }
            Instruction::If(cond, then, els) => {
                let body_sets = live_if(after, cond, then, els);
                after = body_sets.last().unwrap().clone();
                sets.extend(body_sets);
            }
            Instruction::Call(target, callee, args) => {
                after = live_call(after, target, callee, args);
                sets.push(after.clone());
            }
            Instruction::Borrow(target, _, place) => {
                after = live_borrow(after, target, place);
                sets.push(after.clone());
            }
            Instruction::Assign(target, value) => {
                after = live_assign(after, target, value);
                sets.push(after.clone());
            }
            Instruction::Return => {
                after = live_return(after);
                sets.push(after.clone());
            }
        };
    }
    if sets.is_empty() {
        return vec![after];
    }
    sets
}

/// Compute the sets of live-before paths for a loop instruction and its body.
fn live_while(
    mut after: HashSet<Path>,
    cond: &Spanned<Operand>,
    body: &[Instruction],
) -> Vec<HashSet<Path>> {
    let mut before = HashSet::<Path>::from(&cond.item);
    loop {
        let mut sets = live_instrs(after, body.iter().rev());
        let mut diff = before.clone();
        diff.extend(sets.last().unwrap().clone());
        if diff == before {
            sets.push(diff);
            return sets;
        } else {
            before = diff;
            after = before.clone();
        }
    }
}

/// Compute the sets of live-before paths for a conditional instructions and its body.
fn live_if(
    after: HashSet<Path>,
    cond: &Spanned<Operand>,
    then: &[Instruction],
    els: &[Instruction],
) -> Vec<HashSet<Path>> {
    let live_then = live_instrs(after.clone(), then.iter().rev());
    let mut sets = live_instrs(after.clone(), els.iter().rev());
    let mut before = HashSet::<Path>::from(&cond.item);
    before.extend(live_then.last().unwrap().clone());
    before.extend(sets.last().unwrap().clone());
    sets.extend(live_then);
    sets.push(before);
    sets
}

/// Compute the set of live-before paths for a call instruction.
fn live_call(
    mut after: HashSet<Path>,
    target: &Spanned<Place>,
    callee: &Spanned<Place>,
    args: &[Spanned<Operand>],
) -> HashSet<Path> {
    if let Some(path) = Option::<Path>::from(&target.item) {
        after.remove(&path);
    }
    if let Some(path) = Option::<Path>::from(&callee.item) {
        after.insert(path);
    }
    for arg in args {
        after.extend(HashSet::<Path>::from(&arg.item));
    }
    after
}

/// Compute the set of live-before paths for a borrow instruction.
fn live_borrow(
    mut after: HashSet<Path>,
    target: &Spanned<Place>,
    place: &Spanned<Place>,
) -> HashSet<Path> {
    if let Some(path) = Option::<Path>::from(&target.item) {
        after.remove(&path);
    }
    if let Some(path) = Option::<Path>::from(&place.item) {
        after.insert(path);
    }
    after
}

/// Compute the set of live-before paths for an assignment instruction.
fn live_assign(
    mut after: HashSet<Path>,
    target: &Spanned<Place>,
    value: &Spanned<Operand>,
) -> HashSet<Path> {
    if let Some(path) = Option::<Path>::from(&target.item) {
        after.remove(&path);
    }
    after.extend(HashSet::<Path>::from(&value.item));
    after
}

/// Compute the set of live-before paths for a return instruction.
fn live_return(mut after: HashSet<Path>) -> HashSet<Path> {
    after.insert(Path {
        local: 0,
        fields: Vec::new(),
    });
    after
}
