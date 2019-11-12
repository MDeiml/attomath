extern crate nom;

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
use std::collections::BTreeMap;

type Judgement = u16;
type Identifier = i16;

#[derive(Debug)]
pub enum ProofError {
    OperatorMismatch,
    VariableMismatch,
    JudgementMismatch,
    ParameterError,
    DVRError,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Theorem {
    conclusion: Statement,
    assumptions: Vec<Statement>,
    dvrs: Vec<DVR>,
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
        let mut substitution = Substitution::with_capacity(max_var as usize + 1); // TODO: Substitution as trait
        substitution.substitution[*b as usize] = Some(std::slice::from_ref(a));
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
        let numbers: Vec<Identifier> = (shift..=shift + max_var).collect();
        for (n, sub) in numbers.iter().zip(substitution.substitution.iter_mut()) {
            if sub.is_none() {
                *sub = Some(std::slice::from_ref(n));
            }
        }
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

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
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
                    expression: OwnedExpression { data: Box::new([]) },
                },
                Statement {
                    judgement: self.judgement + 1,
                    expression: OwnedExpression { data: Box::new([]) },
                },
            )
        }
    }
}

#[derive(Debug)]
pub struct Substitution<'a> {
    substitution: Vec<Option<&'a [Identifier]>>,
}

impl<'a> Substitution<'a> {
    pub fn with_capacity(n: usize) -> Self {
        Substitution {
            substitution: vec![None; n],
        }
    }

    pub fn get_substitution(&self, id: &'a Identifier) -> &'a [Identifier] {
        self.substitution[*id as usize].unwrap_or(std::slice::from_ref(id))
    }

    pub fn format(&self, formatter: &Formatter) -> String {
        self.substitution
            .iter()
            .enumerate()
            .flat_map(|(i, e)| {
                e.map(|e| {
                    format!(
                        "{} ~> {}",
                        formatter.format_variable(&(i as Identifier)),
                        e.format(formatter)
                    )
                })
            })
            .fold(None, |acc, line| {
                Some(acc.map(|a| a + "\n").unwrap_or(String::new()) + &line)
            })
            .unwrap_or(String::new())
    }
}

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
                if let Some(old) = substitution.substitution[*symb as usize] {
                    data_index += old.len();
                    if old != &data[start..data_index] {
                        return Err(ProofError::VariableMismatch);
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
                    substitution.substitution[*symb as usize] = Some(slice);
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

fn is_operator(x: &Identifier) -> bool {
    x < &0
}

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
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

pub struct Formatter {
    operators: Vec<(&'static str, bool)>,
    judgements: Vec<&'static str>,
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

    fn parse_judgement<'a>(
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

pub struct MemoryDatabase {
    theorems: Vec<Theorem>,
    by_conclusion: BTreeMap<Statement, usize>,
}

impl MemoryDatabase {
    pub fn new() -> Self {
        MemoryDatabase {
            theorems: Vec::new(),
            by_conclusion: BTreeMap::new(),
        }
    }
}

impl<'a> Database for MemoryDatabase {
    fn get(&self, index: usize) -> &Theorem {
        &self.theorems[index]
    }

    fn insert(&mut self, theorem: Theorem) -> usize {
        let index = self.theorems.len();
        self.theorems.push(theorem);
        self.by_conclusion
            .insert(self.theorems[index].conclusion.clone(), index);
        index
    }

    fn conclusion_matching<'b>(
        &'b self,
        conclusion: &Statement,
    ) -> Box<dyn Iterator<Item = &Theorem> + 'b> {
        let (from, to) = conclusion.match_bounds();
        Box::new(
            self.by_conclusion
                .range(from..to)
                .map(move |(_, i)| &self.theorems[*i]),
        )
    }
}

trait Database {
    fn get(&self, index: usize) -> &Theorem;
    fn insert(&mut self, theorem: Theorem) -> usize;
    fn conclusion_matching<'a>(
        &'a self,
        conclusion: &Statement,
    ) -> Box<dyn Iterator<Item = &Theorem> + 'a>;
}

fn parse_statement<'a>(fmt: &Formatter, input: &'a str) -> Statement {
    all_consuming(|s| Statement::parse(fmt, s))(input)
        .unwrap()
        .1
}

fn parse_theorem<'a>(fmt: &Formatter, input: &'a str) -> Theorem {
    all_consuming(|s| Theorem::parse(fmt, s))(input).unwrap().1
}

fn main() {
    let fmt = Formatter {
        operators: vec![("->", true), ("-.", false)],
        judgements: vec!["wff", "|-"],
    };
    let mut db = MemoryDatabase::new();
    let wff2 = parse_theorem(&fmt, "wff x0, wff x1 => wff (x0 -> x1)");
    let ax1 = parse_theorem(&fmt, "wff x0, wff x1 => |- (x0 -> (x1 -> x0))");
    let ax2 = parse_theorem(
        &fmt,
        "wff x0, wff x1, wff x2 => |- ((x0 -> (x1 -> x2)) -> ((x0 -> x1) -> (x0 -> x2)))",
    );
    let ax_mp = parse_theorem(&fmt, "|- x0, |- (x0 -> x1) => |- x1");
    db.insert(wff2);
    db.insert(ax1);
    db.insert(ax2);
    db.insert(ax_mp);
    let test = parse_statement(&fmt, "|- ((x0 -> x1) -> x2)");
    for th in db.conclusion_matching(&test) {
        println!("{}", th.format(&fmt));
    }

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
    // println!("wff (->): {}", wff2.format(&fmt));
    // println!("ax1: {}", ax1.format(&fmt));
    // println!("ax2: {}", ax2.format(&fmt));
    // println!("ax_mp: {}", ax_mp.format(&fmt));
    // println!("{}", t1.format(&fmt));
    // println!("{}", w1.format(&fmt));
    // println!("{}", t2.format(&fmt));
    // println!("{}", t3.format(&fmt));
    // println!("{}", t4.format(&fmt));
    // println!("{}", t5.format(&fmt));
    // println!("{}", t6.format(&fmt));
    // println!("{}", t7.format(&fmt));
    // println!("{}", t8.format(&fmt));
    // println!("{}", t9.format(&fmt));
    // println!("{}", t10.format(&fmt));
}
