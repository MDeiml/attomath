use crate::types::*;

/// A error which is produced when trying to proof something incorrect
#[derive(Debug, PartialEq, Eq)]
pub enum ProofError {
    OperatorMismatch(Identifier, Identifier),
    VariableMismatch(Identifier, Box<[Identifier]>, Box<[Identifier]>),
    JudgementMismatch(Judgement, Judgement),
    ParameterError(usize, usize),
    DVRError(Identifier),
}
