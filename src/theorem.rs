use crate::{
    dvr::DVR,
    error::ProofError,
    expression::{is_operator, Expression},
    formatter::Formatter,
    schema::theorem,
    statement::Statement,
    substitution::Substitution,
    types::*,
};
use diesel::prelude::*;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, space0, space1},
    combinator::map,
    error::VerboseError,
    multi::separated_list,
    sequence::tuple,
    IResult,
};

#[derive(Insertable, Queryable)]
#[table_name = "theorem"]
pub struct DBTheorem {
    id: i32,
    conclusion: Vec<u8>,
    assumptions: Vec<u8>,
    dvrs: Vec<u8>,
    description: Option<String>,
    last_auto: i32,
    use_for_proof: i32,
}

impl DBTheorem {
    pub fn id(&self) -> i32 {
        self.id
    }

    pub fn insert_without_id(conn: &SqliteConnection, theorem1: &Theorem, use_for_proof1: bool) {
        use crate::schema::theorem::dsl::*;
        diesel::insert_into(theorem)
            .values((
                conclusion.eq(&theorem1.conclusion.serialize()),
                assumptions.eq(Statement::serialize_vec(&theorem1.assumptions)),
                dvrs.eq(DVR::serialize_vec(&theorem1.dvrs)),
                use_for_proof.eq(if use_for_proof1 { 1 } else { 0 }),
            ))
            .execute(conn)
            .unwrap();
    }

    pub fn insert_without_ids(conn: &SqliteConnection, theorems: &Vec<Theorem>) {
        use crate::schema::theorem::dsl::*;
        let vals = theorems
            .iter()
            .map(|t| {
                (
                    conclusion.eq(t.conclusion.serialize()),
                    assumptions.eq(Statement::serialize_vec(&t.assumptions)),
                    dvrs.eq(DVR::serialize_vec(&t.dvrs)),
                )
            })
            .collect::<Vec<_>>();
        diesel::insert_or_ignore_into(theorem)
            .values(vals)
            .execute(conn)
            .unwrap();
    }

    pub fn last_auto(&self) -> i32 {
        self.last_auto
    }

    pub fn from_theorem(
        id: i32,
        theorem: &Theorem,
        description: Option<String>,
        last_auto: i32,
        use_for_proof: bool,
    ) -> Self {
        DBTheorem {
            id,
            conclusion: theorem.conclusion.serialize(),
            assumptions: Statement::serialize_vec(&theorem.assumptions),
            dvrs: DVR::serialize_vec(&theorem.dvrs),
            description,
            last_auto,
            use_for_proof: if use_for_proof { 1 } else { 0 },
        }
    }

    pub fn to_theorem(&self) -> Theorem {
        Theorem {
            conclusion: Statement::deserialize(&self.conclusion),
            assumptions: Statement::deserialize_vec(&self.assumptions),
            dvrs: DVR::deserialize_vec(&self.dvrs),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Theorem {
    conclusion: Statement,
    assumptions: Vec<Statement>,
    dvrs: Vec<DVR>,
}

impl Theorem {
    pub fn conclusion(&self) -> &Statement {
        &self.conclusion
    }

    pub fn assumptions(&self) -> &[Statement] {
        &self.assumptions
    }

    pub fn parse<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Self, VerboseError<&'a str>> {
        enum StatementOrDVR {
            Statement(Statement),
            DVR(DVR),
        }
        map(
            tuple((
                separated_list(
                    tuple((space0, char(','), space0)),
                    alt((
                        map(
                            |s| Statement::parse(fmt, s),
                            |s| StatementOrDVR::Statement(s),
                        ),
                        map(|s| DVR::parse(fmt, s), |dvr| StatementOrDVR::DVR(dvr)),
                    )),
                ),
                space1,
                tag("=>"),
                space1,
                |s| Statement::parse(fmt, s),
            )),
            |(pre, _, _, _, conclusion)| {
                let mut assumptions = Vec::new();
                let mut dvrs = Vec::new();
                for sod in pre {
                    match sod {
                        StatementOrDVR::Statement(s) => assumptions.push(s),
                        StatementOrDVR::DVR(dvr) => dvrs.push(dvr),
                    }
                }
                let mut t = Theorem {
                    conclusion,
                    assumptions,
                    dvrs,
                };
                t.standardize();
                t
            },
        )(input)
    }

    pub fn standardize(&mut self) {
        let max_var = self.max_var();
        let mut var_map = vec![None; max_var as usize + 1];
        let mut next_var = 0;
        self.conclusion.standardize(&mut var_map, &mut next_var);
        for a in self.assumptions.iter_mut() {
            a.standardize(&mut var_map, &mut next_var);
        }
        for dvr in self.dvrs.iter_mut() {
            dvr.standardize(&var_map);
        }
        self.assumptions.sort();
        self.dvrs.sort();
    }

    pub fn format(&self, fmt: &Formatter) -> String {
        let preamble = self
            .dvrs
            .iter()
            .map(|dvr| dvr.format(&fmt))
            .chain(self.assumptions.iter().map(|s| s.format(fmt)))
            .fold(None, |s, e| {
                Some(s.map(|s| s + ", ").unwrap_or(String::new()) + &e)
            })
            .map(|s| s + " => ")
            .unwrap_or(String::new());
        preamble + &self.conclusion.format(fmt)
    }

    pub fn max_var(&self) -> Identifier {
        *self
            .conclusion
            .expression
            .get_data()
            .iter()
            .chain(
                self.assumptions
                    .iter()
                    .map(|st| st.expression.get_data().iter())
                    .flatten(),
            )
            .filter(|symb| !is_operator(symb))
            .max()
            .unwrap_or(&-1)
    }

    fn substitute(
        &self,
        substitution: &Substitution,
        skip_assumption: Option<usize>,
    ) -> Result<Self, ProofError> {
        let conclusion = self.conclusion.substitute(substitution);
        let mut assumptions: Vec<Statement> = self
            .assumptions
            .iter()
            .enumerate()
            .filter_map(|(i, a)| {
                if Some(i) == skip_assumption {
                    None
                } else {
                    Some(a)
                }
            })
            .map(|a| a.substitute(substitution))
            .collect();
        assumptions.dedup();
        let dvrs: Result<Vec<DVR>, ProofError> = self
            .dvrs
            .iter()
            .map(|dvr| dvr.substitute(substitution))
            .flatten()
            .collect();
        let mut dvrs = dvrs?;
        dvrs.dedup();
        Ok(Theorem {
            conclusion,
            assumptions,
            dvrs,
        })
    }

    pub fn simplify(&self, a: &Identifier, b: &Identifier) -> Result<Self, ProofError> {
        if is_operator(a) || is_operator(b) {
            return Err(ProofError::ParameterError);
        }
        let max_var = self.max_var();
        if a > &max_var || b > &max_var {
            return Err(ProofError::ParameterError);
        }
        let substitution = Substitution::single_substitution(max_var as usize + 1, a, b);
        let mut t = self.substitute(&substitution, None)?;
        t.standardize();
        Ok(t)
    }

    pub fn combine(&self, other: &Theorem, index: usize) -> Result<Self, ProofError> {
        if index > self.assumptions.len() {
            return Err(ProofError::ParameterError);
        }
        let max_var = self.max_var();
        let mut substitution = Substitution::with_capacity(max_var as usize + 1);
        other
            .conclusion
            .unify(&self.assumptions[index], &mut substitution)?;
        let shift = other.max_var() + 1;
        let numbers = (shift..=shift + max_var as Identifier + 1).collect();
        substitution.substitute_remaining(&numbers);
        let mut t = self.substitute(&substitution, Some(index))?;
        t.assumptions.extend_from_slice(&other.assumptions);
        t.assumptions.dedup();
        t.assumptions.shrink_to_fit();
        t.dvrs.extend_from_slice(&other.dvrs);
        t.dvrs.dedup();
        t.dvrs.shrink_to_fit();
        t.standardize();
        Ok(t)
    }
}
