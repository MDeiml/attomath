use crate::{error::ProofError, types::*};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{char, digit1, space0, space1},
    combinator::{all_consuming, map, map_opt},
    error::{context, VerboseError},
    multi::separated_list,
    sequence::{delimited, preceded, tuple},
    IResult,
};

pub struct Formatter {
    pub operators: Vec<(&'static str, bool)>,
    pub judgements: Vec<&'static str>,
}

impl Formatter {
    pub fn format_variable(&self, id: &Identifier) -> String {
        format!("x{}", id)
    }

    pub fn format_operator(&self, id: &Identifier, left: &str, right: &str) -> String {
        let (op, infix) = self.operators[(-2 - *id) as usize];
        if infix {
            format!("({} {} {})", left, op, right)
        } else {
            format!("({} {} {})", op, left, right)
        }
    }

    pub fn format_judgement(&self, id: &Judgement) -> String {
        self.judgements[*id as usize].to_owned()
    }

    pub fn parse_judgement<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Judgement, VerboseError<&'a str>> {
        map_opt(
            take_while1(|c: char| {
                c.is_ascii_alphanumeric()
                    || (c.is_ascii_punctuation() && c != ',' && c != '(' && c != ')')
            }),
            |s| {
                self.judgements
                    .iter()
                    .position(|j| j == &s)
                    .map(|j| j as Judgement)
            },
        )(input)
    }

    fn parse_operator_helper<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, (Identifier, bool), VerboseError<&'a str>> {
        map_opt(
            take_while1(|c: char| {
                c.is_ascii_alphanumeric()
                    || (c.is_ascii_punctuation() && c != ',' && c != '(' && c != ')')
            }),
            |s| {
                self.operators
                    .iter()
                    .position(|(t, _)| t == &s)
                    .map(|i| (-2 - i as Identifier, self.operators[i].1))
            },
        )(input)
    }

    pub fn parse_operator<'a, A, F: Fn(&str) -> IResult<&str, A, VerboseError<&str>>>(
        &self,
        input: &'a str,
        p: F,
    ) -> IResult<&'a str, (Identifier, A, A), VerboseError<&'a str>> {
        delimited(
            char('('),
            alt((
                context(
                    "prefix",
                    map(
                        tuple((
                            space0,
                            map_opt(
                                |s| self.parse_operator_helper(s),
                                |(i, b)| if !b { Some(i) } else { None },
                            ),
                            space1,
                            &p,
                            space0,
                            &p,
                            space0,
                        )),
                        |(_, a, _, b, _, c, _)| (a, b, c),
                    ),
                ),
                context(
                    "infix",
                    map(
                        tuple((
                            space0,
                            &p,
                            space1,
                            map_opt(
                                |s| self.parse_operator_helper(s),
                                |(i, b)| {
                                    if b {
                                        Some(i)
                                    } else {
                                        None
                                    }
                                },
                            ),
                            space1,
                            &p,
                            space0,
                        )),
                        |(_, a, _, b, _, c, _)| (b, a, c),
                    ),
                ),
            )),
            char(')'),
        )(input)
    }

    pub fn parse_variable<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Identifier, VerboseError<&'a str>> {
        map_opt(preceded(char('x'), digit1), |id: &str| id.parse().ok())(input)
    }
}
