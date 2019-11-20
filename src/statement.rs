use crate::{
    error::ProofError,
    expression::{Expression, Substitution, WholeSubstitution},
    types::*,
};
use std::borrow::Borrow;

pub type OwnedStatement = Statement<Box<[Identifier]>>;

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
pub struct Statement<T: Borrow<[Identifier]>> {
    pub judgement: Judgement,
    pub expression: Expression<T>,
}

/// A a combination of a judgement and an expression, e.g. _x0 -> x0 is provable_
///
/// The __judgement__ is given in form of an integer, but often represents some meaning, like _this
/// expression is provable_ or _this expression is syntactically correct_.
///
/// The __expression__ is a sequence of integers, with the following meaning:
/// * A non-negative integer stands for a __variable__ uniquely identified by this integer
/// * A integer less or equal to `-2` stands for an __operator__. The operator has no associated
/// meaning in this context, but in a normal usecase could represent some expression or operation,
/// e.g. an implication or an addition
/// * The integer `-1` is a __special constant__ node to be used for operators with arity 0 or 1
///
/// A valid expression must have of one of the following formats:
/// * A __variable__, or the __special constant__ `-1`
/// * A __operator__, followed by two valid expression (the operands)
///
/// For example a valid sequences would be `[-2, 0, -2, 1, 0]` or `[-3, -2, 0, 0, -1]` which could
/// stand for _x0 -> (x1 -> x0)_ or _not (x0 -> x0)_ respectively.
///
/// To create operators of arity 0 and 1, one can use the __special constant__ `-1`. For example
/// `-2, 0, -1` is a valid expression which could stand for _not x0_.
///
/// To create operators of arity 3 or higher, one can split the up into multiple operators of artiy
/// 2.
/// For example `-2, 0, -3, 1, 2` is a valid sequence which could stand for _if x0 then x1 else x2_
impl<T: Borrow<[Identifier]> + std::fmt::Debug> Statement<T> {
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
