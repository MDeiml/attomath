use crate::{
    error::ProofError, expression::is_operator, formatter::Formatter, substitution::Substitution,
    types::*,
};
use nom::{
    character::complete::{char, space1},
    combinator::map_opt,
    error::VerboseError,
    sequence::tuple,
    IResult,
};

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct DVR(Identifier, Identifier);

impl DVR {
    pub fn serialize_vec(dvrs: &Vec<DVR>) -> Vec<u8> {
        let mut res = Vec::with_capacity(dvrs.len() * 2 * 2);
        for DVR(a, b) in dvrs {
            res.push((a >> 8) as u8);
            res.push((a & 0xff) as u8);
            res.push((b >> 8) as u8);
            res.push((b & 0xff) as u8);
        }
        res
    }

    pub fn deserialize_vec(raw: &[u8]) -> Vec<Self> {
        let mut res = Vec::with_capacity(raw.len() / 4);
        for i in 0..raw.len() / 4 {
            let a = ((raw[4 * i] as i16) << 8) | raw[4 * i + 1] as i16;
            let b = ((raw[4 * i + 2] as i16) << 8) | raw[4 * i + 3] as i16;
            res.push(DVR::new(a, b).unwrap());
        }
        res
    }

    pub fn format(&self, fmt: &Formatter) -> String {
        let DVR(a, b) = self;
        format!("{} <> {}", fmt.format_variable(&a), fmt.format_variable(&b))
    }

    pub fn new(a: Identifier, b: Identifier) -> Result<Self, ProofError> {
        if a < b {
            Ok(DVR(a, b))
        } else if a > b {
            Ok(DVR(b, a))
        } else {
            Err(ProofError::DVRError)
        }
    }

    pub fn substitute<'a>(
        &'a self,
        substitution: &'a Substitution,
    ) -> impl Iterator<Item = Result<Self, ProofError>> + 'a {
        let DVR(a, b) = self;
        let sub_a = substitution.get_substitution(a);
        let sub_b = substitution.get_substitution(b);
        sub_a
            .iter()
            .filter(|symb| !is_operator(symb))
            .map(move |new_a| {
                sub_b
                    .iter()
                    .filter(|symb| !is_operator(symb))
                    .map(move |new_b| Self::new(*new_a, *new_b))
            })
            .flatten()
    }

    pub fn standardize(&mut self, var_map: &Vec<Option<Identifier>>) {
        let DVR(a, b) = self;
        *a = var_map[*a as usize].expect("DVR with free variable");
        *b = var_map[*b as usize].expect("DVR with free variable");
        if a > b {
            let temp = *a;
            *a = *b;
            *b = temp;
        }
    }

    pub fn parse<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Self, VerboseError<&'a str>> {
        map_opt(
            tuple((
                char('d'),
                space1,
                |s| fmt.parse_variable(s),
                space1,
                |s| fmt.parse_variable(s),
            )),
            |(_, _, a, _, b)| Self::new(a, b).ok(),
        )(input)
    }
}
