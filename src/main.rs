#[macro_use]
extern crate diesel;
extern crate bincode;
extern crate nom;
extern crate serde;

pub mod error;
pub mod expression;
pub mod formatter;
pub mod schema;
pub mod substitution;
pub mod types;

use diesel::prelude::*;
use diesel::sqlite::{Sqlite, SqliteConnection};
use error::ProofError;
use expression::{is_operator, Expression, OwnedExpression};
use formatter::Formatter;
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
use schema::*;
use serde::{Deserialize, Serialize};
use substitution::Substitution;
use types::*;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Theorem {
    conclusion: Statement,
    assumptions: Vec<Statement>,
    dvrs: Vec<DVR>,
}

#[derive(Insertable)]
#[table_name = "theorem"]
pub struct DBInsertTheorem {
    conclusion: Vec<u8>,
    assumptions: Vec<u8>,
    dvrs: Vec<u8>,
    description: Option<String>,
}

impl Insertable<theorem::table> for &Theorem {
    type Values = <DBInsertTheorem as Insertable<theorem::table>>::Values;

    fn values(self) -> Self::Values {
        Insertable::values(DBInsertTheorem {
            conclusion: bincode::serialize(&self.conclusion).unwrap(),
            assumptions: bincode::serialize(&self.assumptions).unwrap(),
            dvrs: bincode::serialize(&self.dvrs).unwrap(),
            description: None,
        })
    }
}

impl Queryable<theorem::SqlType, DB> for Theorem {
    type Row = (i32, Vec<u8>, Vec<u8>, Vec<u8>, Option<String>);

    fn build((_id, conclusion, assumptions, dvrs, _name): Self::Row) -> Self {
        Theorem {
            conclusion: bincode::deserialize(&conclusion).unwrap(),
            assumptions: bincode::deserialize(&assumptions).unwrap(),
            dvrs: bincode::deserialize(&dvrs).unwrap(),
        }
    }
}

impl Theorem {
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
            .map(|DVR(a, b)| format!("{} {}", fmt.format_variable(&a), fmt.format_variable(&b)))
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

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Statement {
    judgement: Judgement,
    expression: OwnedExpression,
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

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Serialize, Deserialize)]
struct DVR(Identifier, Identifier);

impl DVR {
    fn new(a: Identifier, b: Identifier) -> Result<Self, ProofError> {
        if a < b {
            Ok(DVR(a, b))
        } else if a > b {
            Ok(DVR(b, a))
        } else {
            Err(ProofError::DVRError)
        }
    }

    fn substitute<'a>(
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

    fn parse<'a>(fmt: &Formatter, input: &'a str) -> IResult<&'a str, Self, VerboseError<&'a str>> {
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

fn parse_theorem<'a>(fmt: &Formatter, input: &'a str) -> Theorem {
    all_consuming(|s| Theorem::parse(fmt, s))(input).unwrap().1
}

fn main() {
    let database_url = "test.db";
    let conn = SqliteConnection::establish(database_url).unwrap();

    let fmt = Formatter {
        operators: vec![("->", true), ("-.", false)],
        judgements: vec!["wff", "|-"],
    };

    let wff2 = parse_theorem(&fmt, "wff x0, wff x1 => wff (x0 -> x1)");
    diesel::insert_into(theorem::table)
        .values(&wff2)
        .execute(&conn)
        .unwrap();
    let ts = (theorem::table).limit(1).load::<Theorem>(&conn).unwrap();
    println!("{}", ts[0].format(&fmt));

    // let wff2 = parse_theorem(&fmt, "wff x0, wff x1 => wff (x0 -> x1)");
    // let ax1 = parse_theorem(&fmt, "wff x0, wff x1 => |- (x0 -> (x1 -> x0))");
    // let ax2 = parse_theorem(
    //     &fmt,
    //     "wff x0, wff x1, wff x2 => |- ((x0 -> (x1 -> x2)) -> ((x0 -> x1) -> (x0 -> x2)))",
    // );
    // let ax_mp = parse_theorem(&fmt, "|- x0, |- (x0 -> x1) => |- x1");

    // let t1 = ax1.simplify(&0, &1).unwrap();
    // let w1 = wff2.simplify(&0, &1).unwrap();
    // let t2 = ax1.combine(&w1, 1).unwrap();
    // let t3 = t2.simplify(&0, &1).unwrap();
    // let t4 = ax2.combine(&w1, 1).unwrap();
    // let t5 = t4.simplify(&0, &1).unwrap();
    // let t6 = t5.simplify(&0, &1).unwrap();
    // let t7 = ax_mp.combine(&t6, 0).unwrap();
    // let t8 = t7.combine(&t3, 1).unwrap();
    // let t9 = ax_mp.combine(&t8, 0).unwrap();
    // let t10 = t9.combine(&t1, 1).unwrap();
}
