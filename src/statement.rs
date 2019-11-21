use crate::{
    error::ProofError,
    expression::{Expression, Substitution, WholeSubstitution},
    types::*,
};
use std::borrow::Borrow;

/// Type alias for a statement that owns its expression
pub type OwnedStatement = Statement<Box<[Identifier]>>;

/// A a combination of a judgement and an `Expression`, for example _x0 -> x0 is provable_
///
/// The __judgement__ is given in form of an integer, but often represents some meaning, like _this
/// expression is provable_ or _this expression is syntactically correct_.
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
pub struct Statement<T: Borrow<[Identifier]>> {
    pub judgement: Judgement,
    pub expression: Expression<T>,
}
impl<T: Borrow<[Identifier]> + std::fmt::Debug> Statement<T> {
    // TODO: Remove weird eq from example
    /// Convenience function for unifying the expressions of two judgements (see
    /// [`Expression::unify`](../expression/struct.Expression.html#method.unify)).
    ///
    /// # Errors
    /// * `JudgementMismatch` - if `self.judgement != other.judgement`
    /// * `VariableMismatch` or `OperatorMismatch` - if `self.expression.unify(other.expression)`
    /// fails
    ///
    /// # Example
    /// ```
    /// use attomath::statement::Statement;
    /// use attomath::expression::{Expression, WholeSubstitution};
    /// use attomath::error::ProofError;
    ///
    /// let st1 = Statement {
    ///     judgement: 0,
    ///     expression: Expression::from_raw(vec![-2, 0, -2, 1, 0].into_boxed_slice()).unwrap()
    /// };
    /// let st2 = Statement {
    ///     judgement: 0,
    ///     expression: Expression::from_raw(vec![-2, 0, 1]).unwrap()
    /// };
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let res = st1.unify(&st2, &mut sub);
    /// assert_eq!(res, Ok(()));
    /// assert_eq!(st2.substitute(&sub), st1);
    ///
    /// let st2 = Statement {
    ///     judgement: 1,
    ///     expression: Expression::from_raw(vec![-2, 0, 1]).unwrap()
    /// };
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let res = st1.unify(&st2, &mut sub);
    /// assert_eq!(res, Err(ProofError::JudgementMismatch(0, 1)));
    /// ```
    pub fn unify<'a, S: Borrow<[Identifier]>>(
        &'a self,
        other: &Statement<S>,
        substitution: &mut WholeSubstitution<'a>,
    ) -> Result<(), ProofError> {
        if self.judgement != other.judgement {
            return Err(ProofError::JudgementMismatch(
                self.judgement,
                other.judgement,
            ));
        }
        self.expression.unify(&other.expression, substitution)?;
        return Ok(());
    }

    /// Convenience function for using a `Substitution` on this judgements expression (see
    /// [`Expression::substitute`](../expression/struct.Expression.html#method.substitute))
    pub fn substitute<'a, S: Substitution<'a>>(
        &self,
        substitution: &'a S,
    ) -> Statement<Box<[Identifier]>> {
        Statement {
            judgement: self.judgement,
            expression: self.expression.substitute(substitution),
        }
    }
}
