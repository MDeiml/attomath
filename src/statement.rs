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

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct Statement {
    pub judgement: Judgement,
    pub expression: OwnedExpression,
}

impl Statement {
    pub fn serialize(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(self.expression.len() * 2 + 2);
        res.push((self.judgement >> 8) as u8);
        res.push((self.judgement & 0xff) as u8);
        self.expression.serialize(&mut res);
        res
    }

    pub fn deserialize(raw: &[u8]) -> Self {
        let judgement = ((raw[0] as u16) << 8) | raw[1] as u16;
        let expression = OwnedExpression::deserialize(&raw[2..raw.len()]);
        Statement {
            judgement,
            expression,
        }
    }

    pub fn serialize_vec(statements: &Vec<Self>) -> Vec<u8> {
        let mut res = Vec::with_capacity(
            statements
                .iter()
                .map(|s| s.expression().len() * 2 + 2 + 8)
                .sum(),
        );
        for s in statements {
            let size = s.expression().len() * 2 + 2;
            for i in 0..8 {
                res.push(((size >> (8 * (8 - i - 1))) & 0xff) as u8);
            }
            res.push((s.judgement >> 8) as u8);
            res.push((s.judgement & 0xff) as u8);
            s.expression.serialize(&mut res);
        }
        res
    }

    pub fn deserialize_vec(raw: &[u8]) -> Vec<Self> {
        let mut res = Vec::new();
        let mut index = 0;
        while index < raw.len() {
            let mut size = 0usize;
            for i in 0..8 {
                size |= (raw[index + i] as usize) << (8 * (8 - i - 1));
            }
            res.push(Self::deserialize(&raw[index + 8..index + 8 + size]));
            index += size + 8;
        }
        res
    }

    pub fn expression(&self) -> &OwnedExpression {
        &self.expression
    }

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
