use crate::types::*;

/// An error which is produced when trying to proof something incorrect
#[derive(Debug, PartialEq, Eq)]
pub enum ProofError {
    /// Error produced when trying to unify expressions with different operators (see
    /// [`Expression::unify`](../expression/struct.Expression.html#method.unify)). Contains the
    /// identifiers of the mismatched operators.
    OperatorMismatch(Identifier, Identifier),
    /// Error produced when trying to unify expressions where one variable would have to be
    /// substituted by different subexpressions (see
    /// [`Expression::unify`](../expression/struct.Expression.html#method.unify)). Contains the
    /// identifier for the variable and the mismatched subexpressions.
    VariableMismatch(Identifier, Box<[Identifier]>, Box<[Identifier]>),
    /// Error produced when trying to unify statements with different judgements (see
    /// [`Statement::unify`](../statement/struct.Statement.html#method.unify)). Contains the
    /// mismatched judgements.
    JudgementMismatch(Judgement, Judgement),
    /// Error produced when trying to create a theorem with conflicting dvrs (see
    /// [`DVR`](../dvr/struct.DVR.html)).
    DVRError(Identifier),
}
