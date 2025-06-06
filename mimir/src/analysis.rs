//! Static analyis module.

use std::collections::HashSet;

use crate::{
    ir::{Instruction, LocalId, Operand, Place},
    reporting::Spanned,
};

/// Compute the sets of live-before paths for a function body.
pub fn liveness(instrs: &[Instruction]) -> Vec<HashSet<Path>> {
    // At the end of a function's body, only its return value is live.
    let state = HashSet::from([Path {
        local: 0,
        fields: Vec::new(),
    }]);
    // Liveness analysis is a backwards analysis, hence the call to `rev`.
    LivenessAnalysis::visit(state, instrs.iter().rev())
}

/// An abstract interpreter for Mimir instructions.
pub trait AbstractInterpreter {
    /// The domain of the states manipulated by the abstract interpreter.
    type Domain: Clone;

    /// Visit a sequence of instructions and compute their abstract states, given some initial state.
    fn visit<'i, I>(mut state: Self::Domain, instrs: I) -> Vec<Self::Domain>
    where
        I: Iterator<Item = &'i Instruction>,
    {
        let mut states = Vec::new();
        for instr in instrs {
            match instr {
                Instruction::While(cond, body) => {
                    let body_states = Self::visit_while(state, cond, body);
                    state = body_states.last().unwrap().clone();
                    states.extend(body_states);
                }
                Instruction::If(cond, then, els) => {
                    let body_states = Self::visit_if(state, cond, then, els);
                    state = body_states.last().unwrap().clone();
                    states.extend(body_states);
                }
                Instruction::Call(target, callee, args) => {
                    state = Self::visit_call(state, target, callee, args);
                    states.push(state.clone());
                }
                Instruction::Borrow(target, _, place) => {
                    state = Self::visit_borrow(state, target, place);
                    states.push(state.clone());
                }
                Instruction::Assign(target, value) => {
                    state = Self::visit_assign(state, target, value);
                    states.push(state.clone());
                }
                Instruction::Return => {
                    state = Self::visit_return(state);
                    states.push(state.clone());
                }
            };
        }
        if states.is_empty() {
            return vec![state];
        }
        states
    }

    /// Visit a loop instruction and compute the abstract states for the instructions it contains,
    /// as well as for the instruction itself.
    fn visit_while(
        state: Self::Domain,
        cond: &Spanned<Operand>,
        body: &[Instruction],
    ) -> Vec<Self::Domain>;

    /// Visit a conditional instruction and compute the abstract states for the instructions it
    /// contains, as well as for the instruction itself.
    fn visit_if(
        state: Self::Domain,
        cond: &Spanned<Operand>,
        then: &[Instruction],
        els: &[Instruction],
    ) -> Vec<Self::Domain>;

    /// Visit a call instruction and compute an abstract state for it.
    fn visit_call(
        state: Self::Domain,
        target: &Spanned<Place>,
        callee: &Spanned<Operand>,
        args: &[Spanned<Operand>],
    ) -> Self::Domain;

    /// Visit a borrow instruction and compute an abstract state for it.
    fn visit_borrow(
        state: Self::Domain,
        target: &Spanned<Place>,
        place: &Spanned<Place>,
    ) -> Self::Domain;

    /// Visit an assignment instruction and compute an abstract state for it.
    fn visit_assign(
        state: Self::Domain,
        target: &Spanned<Place>,
        value: &Spanned<Operand>,
    ) -> Self::Domain;

    /// Visit a return instruction and compute an abstract state for it.
    fn visit_return(state: Self::Domain) -> Self::Domain;
}

/// An abstract interpreter that computes the sets of live-before paths for instructions.
struct LivenessAnalysis;

impl AbstractInterpreter for LivenessAnalysis {
    type Domain = HashSet<Path>;

    fn visit_while(
        mut state: Self::Domain,
        cond: &Spanned<Operand>,
        body: &[Instruction],
    ) -> Vec<Self::Domain> {
        let mut before = HashSet::<Path>::from(&cond.item);
        loop {
            let mut states = Self::visit(state, body.iter().rev());
            let mut diff = before.clone();
            diff.extend(states.last().unwrap().clone());
            if diff == before {
                states.push(diff);
                return states;
            } else {
                before = diff;
                state = before.clone();
            }
        }
    }

    fn visit_if(
        state: Self::Domain,
        cond: &Spanned<Operand>,
        then: &[Instruction],
        els: &[Instruction],
    ) -> Vec<Self::Domain> {
        let live_then = Self::visit(state.clone(), then.iter().rev());
        let mut states = Self::visit(state.clone(), els.iter().rev());
        let mut before = HashSet::<Path>::from(&cond.item);
        before.extend(live_then.last().unwrap().clone());
        before.extend(states.last().unwrap().clone());
        states.extend(live_then);
        states.push(before);
        states
    }

    fn visit_call(
        mut state: Self::Domain,
        target: &Spanned<Place>,
        callee: &Spanned<Operand>,
        args: &[Spanned<Operand>],
    ) -> Self::Domain {
        state.remove(&Path::from(&target.item));
        state.extend(HashSet::<Path>::from(&callee.item));
        for arg in args {
            state.extend(HashSet::<Path>::from(&arg.item));
        }
        state
    }

    fn visit_borrow(
        mut state: Self::Domain,
        target: &Spanned<Place>,
        place: &Spanned<Place>,
    ) -> Self::Domain {
        state.remove(&Path::from(&target.item));
        state.insert(Path::from(&place.item));
        state
    }

    fn visit_assign(
        mut state: Self::Domain,
        target: &Spanned<Place>,
        value: &Spanned<Operand>,
    ) -> Self::Domain {
        state.remove(&Path::from(&target.item));
        state.extend(HashSet::<Path>::from(&value.item));
        state
    }

    fn visit_return(mut state: Self::Domain) -> Self::Domain {
        state.insert(Path {
            local: 0,
            fields: Vec::new(),
        });
        state
    }
}

/// A path to an aliasable memory location.
/// A path corresponds to a local identifier followed by an arbitrary number of field indices.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Path {
    pub local: LocalId,
    pub fields: Vec<usize>,
}

impl From<&Place> for Path {
    /// Compute the path in a place expression.
    fn from(value: &Place) -> Self {
        match &value {
            Place::Field(place, index) => {
                let mut path = Path::from(&place.item);
                path.fields.push(index.item);
                path
            }
            Place::Deref(place) => Path::from(&place.item),
            Place::Local(id) => Path {
                local: *id,
                fields: Vec::new(),
            },
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
            Operand::Place(place) => HashSet::from([Path::from(place)]),
            Operand::Fn(_, _) | Operand::Int(_) | Operand::Bool(_) => HashSet::new(),
        }
    }
}
