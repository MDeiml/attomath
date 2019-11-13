use crate::{
    error::ProofError,
    expression::{Expression, OwnedExpression},
    formatter::Formatter,
    substitution::Substitution,
    types::*,
};
use nom::{
    character::complete::space1, combinator::map, error::VerboseError, sequence::tuple, IResult,
};
use serde::{Deserialize, Serialize};

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Statement {
    pub judgement: Judgement,
    pub expression: OwnedExpression,
}

impl Statement {
    pub fn standardize(
        &mut self,
        var_map: &mut Vec<Option<Identifier>>,
        next_var: &mut Identifier,
    ) {
        self.expression.standardize(var_map, next_var);
    }

    pub fn format(&self, fmt: &Formatter) -> String {
        format!(
            "{} {}",
            fmt.format_judgement(&self.judgement),
            self.expression.format(fmt)
        )
    }

    pub fn substitute(&self, substitution: &Substitution) -> Self {
        Statement {
            judgement: self.judgement,
            expression: self.expression.substitute(substitution),
        }
    }

    pub fn unify<'a>(
        &'a self,
        other: &Self,
        substitution: &mut Substitution<'a>,
    ) -> Result<(), ProofError> {
        if self.judgement != other.judgement {
            return Err(ProofError::JudgementMismatch);
        }
        self.expression.unify(&other.expression, substitution)
    }

    pub fn parse<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Self, VerboseError<&'a str>> {
        map(
            tuple((
                |s| fmt.parse_judgement(s),
                space1,
                |s| OwnedExpression::parse(fmt, s),
            )),
            |(j, _, e)| Statement {
                judgement: j,
                expression: e,
            },
        )(input)
    }

    pub fn match_bounds(&self) -> (Self, Self) {
        if let Some((low, high)) = self.expression.match_bounds() {
            (
                Statement {
                    judgement: self.judgement,
                    expression: low,
                },
                Statement {
                    judgement: self.judgement,
                    expression: high,
                },
            )
        } else {
            (
                Statement {
                    judgement: self.judgement,
                    expression: OwnedExpression::empty(),
                },
                Statement {
                    judgement: self.judgement + 1,
                    expression: OwnedExpression::empty(),
                },
            )
        }
    }
}
