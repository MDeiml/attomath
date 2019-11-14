use crate::{error::ProofError, formatter::Formatter, substitution::Substitution, types::*};
use nom::{
    branch::alt,
    combinator::map,
    error::{context, VerboseError},
    IResult,
};

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct OwnedExpression {
    data: Box<[Identifier]>,
}

impl Expression for OwnedExpression {
    fn get_data<'a>(&'a self) -> &'a [Identifier] {
        &self.data
    }
}

impl OwnedExpression {
    pub fn deserialize(raw: &[u8]) -> Self {
        let mut data = Vec::with_capacity(raw.len() / 2);
        for i in 0..raw.len() / 2 {
            data.push(((raw[2 * i] as i16) << 8) | (raw[2 * i + 1] as i16));
        }
        OwnedExpression {
            data: data.into_boxed_slice(),
        }
    }

    pub fn empty() -> Self {
        OwnedExpression {
            data: Vec::new().into_boxed_slice(),
        }
    }

    pub fn check(&self) -> bool {
        let data = self.get_data();
        let mut depth = 1;
        for s in data {
            if is_operator(s) && s != &-1 {
                depth += 1;
            } else {
                depth -= 1;
            }
        }
        depth == 0
    }

    pub fn standardize(
        &mut self,
        var_map: &mut Vec<Option<Identifier>>,
        next_var: &mut Identifier,
    ) {
        for symb in self.data.iter_mut() {
            if !is_operator(symb) {
                *symb = var_map[*symb as usize].unwrap_or_else(|| {
                    let var = *next_var;
                    var_map[*symb as usize] = Some(var);
                    *next_var += 1;
                    var
                });
            }
        }
    }

    pub fn parse_helper<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Vec<Identifier>, VerboseError<&'a str>> {
        alt((
            context("variable", map(|s| fmt.parse_variable(s), |v| vec![v])),
            context(
                "operator",
                map(
                    |s| fmt.parse_operator(s, |t| Self::parse_helper(fmt, t)),
                    |(a, b, c)| {
                        let mut res = vec![a];
                        res.extend_from_slice(&b);
                        res.extend_from_slice(&c);
                        res
                    },
                ),
            ),
            context("empty_op", |s| Ok((s, vec![-1]))),
        ))(input)
    }

    pub fn parse<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Self, VerboseError<&'a str>> {
        context(
            "expression",
            map(
                |s| Self::parse_helper(fmt, s),
                |v| OwnedExpression {
                    data: v.into_boxed_slice(),
                },
            ),
        )(input)
    }
}

impl<'a> Expression for &'a [Identifier] {
    fn get_data<'b>(&'b self) -> &'b [Identifier] {
        self
    }
}

pub trait Expression: Ord {
    fn serialize(&self, res: &mut Vec<u8>) {
        let data = self.get_data();
        for s in data {
            res.push((s >> 8) as u8);
            res.push((s & 0xff) as u8);
        }
    }

    fn len(&self) -> usize {
        self.get_data().len()
    }

    fn get_data<'a>(&'a self) -> &'a [Identifier];
    // TODO: Return result
    fn unify<'a>(
        &'a self,
        other: &Self,
        substitution: &mut Substitution<'a>,
    ) -> Result<(), ProofError> {
        let data = self.get_data();
        let mut data_iter = data.iter();
        let mut data_index = 0;
        for symb in other.get_data().iter() {
            if is_operator(&symb) {
                let symb_self = data_iter
                    .next()
                    .expect(format!("self is not well formated {:?}", data).as_str());
                data_index += 1;
                if symb_self != symb {
                    return Err(ProofError::OperatorMismatch);
                }
            } else {
                let mut depth = 1;
                let start = data_index;
                if let Some(old) = substitution.get_substitution_opt(symb) {
                    data_index += old.len();
                    if data.len() < data_index || old != &data[start..data_index] {
                        return Err(ProofError::VariableMismatch);
                    }
                    for _ in 0..old.len() {
                        data_iter.next();
                    }
                } else {
                    let slice = loop {
                        let s = data_iter
                            .next()
                            .expect(format!("self is not well formated {:?}", data).as_str());
                        data_index += 1;
                        if is_operator(s) && s != &-1 {
                            depth += 1;
                        } else {
                            depth -= 1;
                        }
                        if depth == 0 {
                            let slice = &data[start..data_index];
                            break slice;
                        }
                    };
                    substitution.insert(symb, slice);
                }
            }
        }
        return Ok(());
    }

    fn substitute<'a>(&self, substitution: &Substitution<'a>) -> OwnedExpression {
        let data = self.get_data();
        let mut new_data = Vec::with_capacity(data.len());
        for symb in data.iter() {
            if is_operator(symb) {
                new_data.push(*symb)
            } else {
                new_data.extend_from_slice(substitution.get_substitution(symb));
            }
        }
        OwnedExpression {
            data: new_data.into_boxed_slice(),
        }
    }

    fn format_helper(s: &[Identifier], formatter: &Formatter) -> (String, usize) {
        let symb = s[0];
        if is_operator(&symb) {
            if symb == -1 {
                ("".to_owned(), 1)
            } else {
                let mut index = 1;
                let (left, len) = Self::format_helper(&s[1..], formatter);
                index += len;
                let (right, len) = Self::format_helper(&s[index..], formatter);
                index += len;
                (
                    formatter.format_operator(&symb, left.as_str(), right.as_str()),
                    index,
                )
            }
        } else {
            (formatter.format_variable(&symb), 1)
        }
    }

    fn format(&self, formatter: &Formatter) -> String {
        Self::format_helper(&self.get_data(), formatter).0
    }

    fn match_bounds(&self) -> Option<(OwnedExpression, OwnedExpression)> {
        let data = self.get_data();
        let index = data
            .iter()
            .position(|s| !is_operator(s))
            .unwrap_or(data.len());
        if index == 0 {
            return None;
        }
        let low = OwnedExpression {
            data: Box::from(&data[0..index]),
        };
        let mut high = OwnedExpression {
            data: Box::from(&data[0..index]),
        };
        high.data[index - 1] += 1;
        Some((low, high))
    }
}

pub fn is_operator(x: &Identifier) -> bool {
    x < &0
}
