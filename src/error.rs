#[derive(Debug)]
pub enum ProofError {
    OperatorMismatch,
    VariableMismatch,
    JudgementMismatch,
    ParameterError,
    DVRError,
    Tautology,
}
