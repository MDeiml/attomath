use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_while1},
    character::complete::char,
    combinator::{eof, map, map_opt, verify},
    error::context,
    multi::separated_list1,
    IResult,
};

// TODO
use crate::{
    dvr::DVR,
    error::GreedyError,
    expression::{is_operator, Expression},
    statement::Statement,
    theorem::Theorem,
    types::*,
    OwnedStatement,
};
use std::borrow::Borrow;
use std::fmt::Write;

/// ```
/// use attomath::formatter::Formatter;
/// use attomath::Expression;
/// use attomath::Theorem;
/// use attomath::Statement;
/// use attomath::DVR;
///
/// let mut fmt = Formatter::new();
/// fmt.add_operator("->".to_owned(), 2);
/// fmt.add_judgement("|-".to_owned());
///
/// let conclusion = Statement {
///     judgement: 0,
///     expression: Expression::from_raw(vec![1].into_boxed_slice()).unwrap()
/// };
/// let assumptions = vec![
///     Statement {
///         judgement: 0,
///         expression: Expression::from_raw(vec![0].into_boxed_slice()).unwrap(),
///     },
///     Statement {
///         judgement: 0,
///         expression: Expression::from_raw(vec![-2, 0, 1].into_boxed_slice()).unwrap(),
///     }
/// ];
/// let dvrs = vec![DVR::new(0, 1).unwrap()];
/// let theorem = Theorem::new(conclusion, assumptions, dvrs);
///
/// let mut s = String::new();
/// fmt.format_theorem(&mut s, &theorem);
/// assert_eq!(s, "a <> b, |- a, |- (a -> b) => |- b");
///
/// let (remaining, theorem1) = fmt.parse_theorem(&s).unwrap();
/// assert_eq!(remaining, "");
/// assert_eq!(theorem1, theorem);
/// ```
pub struct Formatter {
    operators: Vec<(String, u8)>,
    judgements: Vec<String>,
}

impl Formatter {
    pub fn new() -> Self {
        Formatter {
            operators: Vec::new(),
            judgements: Vec::new(),
        }
    }

    pub fn add_operator(&mut self, operator: String, arity: u8) {
        // TODO: verify
        self.operators.push((operator, arity));
    }

    pub fn add_judgement(&mut self, judgement: String) {
        // TODO: verify
        self.judgements.push(judgement);
    }

    pub fn format_operator<T: Borrow<[Identifier]> + std::fmt::Debug>(
        &self,
        s: &mut String,
        id: Identifier,
        left: &Expression<T>,
        right: &Expression<T>,
    ) {
        if id == Identifier::MIN {
            return;
        }
        let (symb, arity) = self.operators[(-id - 2) as usize].clone();
        if arity == 0 {
            write!(s, "{}", symb).unwrap();
        } else if arity == 1 {
            write!(s, "({} ", symb).unwrap();
            self.format_expression(s, left);
            s.push(')');
        } else if arity == 2 {
            s.push('(');
            self.format_expression(s, left);
            write!(s, " {} ", symb).unwrap();
            self.format_expression(s, right);
            s.push(')');
        } else {
            unimplemented!()
        }
    }

    pub fn parse_arity<'a>(
        &self,
        arity: u8,
        input: &'a str,
    ) -> IResult<&'a str, Expression<Box<[Identifier]>>, GreedyError<&'a str>> {
        if arity == 0 {
            let (input, o) = map_opt(is_not(" ),"), |s| {
                self.operators
                    .iter()
                    .enumerate()
                    .filter_map(|(i, (o, a))| if s == o && *a == 0 { Some(i) } else { None })
                    .next()
            })(input)?;
            // TODO: remove unwrap
            Ok((
                input,
                Expression::from_raw(
                    vec![-(o as Identifier) - 2, Identifier::MIN, Identifier::MIN]
                        .into_boxed_slice(),
                )
                .unwrap(),
            ))
        } else if arity == 1 {
            let (input, _) = char('(')(input)?;
            let (input, o) = map_opt(is_not(" ),"), |s| {
                self.operators
                    .iter()
                    .enumerate()
                    .filter_map(|(i, (o, a))| if s == o && *a == 1 { Some(i) } else { None })
                    .next()
            })(input)?;
            let (input, _) = char(' ')(input)?;
            let (input, left) = self.parse_expression(input)?;
            let (input, _) = char(')')(input)?;
            let mut data = Vec::with_capacity(left.data().len() + 2);
            data.push(-(o as Identifier) - 2);
            data.extend_from_slice(left.data());
            data.push(Identifier::MIN);
            // TODO: remove unwrap
            Ok((
                input,
                Expression::from_raw(data.into_boxed_slice()).unwrap(),
            ))
        } else if arity == 2 {
            let (input, _) = char('(')(input)?;
            let (input, left) = self.parse_expression(input)?;
            let (input, _) = char(' ')(input)?;
            let (input, o) = map_opt(is_not(" ),"), |s| {
                self.operators
                    .iter()
                    .enumerate()
                    .filter_map(|(i, (o, a))| if s == o && *a == 2 { Some(i) } else { None })
                    .next()
            })(input)?;
            let (input, _) = char(' ')(input)?;
            let (input, right) = self.parse_expression(input)?;
            let (input, _) = char(')')(input)?;
            let mut data = Vec::with_capacity(left.data().len() + right.data().len() + 1);
            data.push(-(o as Identifier) - 2);
            data.extend_from_slice(left.data());
            data.extend_from_slice(right.data());
            // TODO: remove unwrap
            Ok((
                input,
                Expression::from_raw(data.into_boxed_slice()).unwrap(),
            ))
        } else {
            unimplemented!()
        }
    }

    pub fn parse_operator<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression<Box<[Identifier]>>, GreedyError<&'a str>> {
        alt((
            |input| self.parse_arity(2, input),
            |input| self.parse_arity(1, input),
            |input| self.parse_arity(0, input),
        ))(input)
    }

    pub fn format_variable(&self, s: &mut String, mut id: Identifier) {
        assert!(id >= 0);
        id += 1;
        s.extend(
            std::iter::from_fn(move || {
                if id == 0 {
                    None
                } else if id <= 26 {
                    let c = ('a' as u8 + (id % 26) as u8 - 1) as char;
                    id = 0;
                    Some(c)
                } else {
                    let c = ('a' as u8 + (id % 26) as u8) as char;
                    id /= 26;
                    Some(c)
                }
            })
            .collect::<Vec<_>>()
            .into_iter(),
        );
    }

    pub fn parse_variable<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Identifier, GreedyError<&'a str>> {
        let (input, var) = take_while1(|c| c >= 'a' && c <= 'z')(input)?;
        let mut id = 0i16;
        for c in var.chars() {
            id *= 26;
            if id == 0 {
                id += 1;
            }
            id += (c as u8 - 'a' as u8) as i16;
        }
        Ok((input, id - 1))
    }

    pub fn format_expression<T: Borrow<[Identifier]> + std::fmt::Debug>(
        &self,
        s: &mut String,
        expression: &Expression<T>,
    ) {
        let id = expression.to_slice().data()[0];
        if id == Identifier::MIN {
            return;
        }
        if is_operator(id) {
            let left = expression.subexpression(1);
            let right = expression.subexpression(1 + left.data().len());
            self.format_operator(s, id, &left, &right);
        } else {
            self.format_variable(s, id)
        }
    }

    pub fn parse_expression<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression<Box<[Identifier]>>, GreedyError<&'a str>> {
        // TODO: remove unwrap
        alt((
            map(
                |input| self.parse_variable(input),
                |v| Expression::from_raw(vec![v].into_boxed_slice()).unwrap(),
            ),
            |input| self.parse_operator(input),
        ))(input)
    }

    pub fn format_judgement(&self, s: &mut String, judgement: Judgement) {
        s.push_str(&self.judgements[judgement as usize]);
    }

    pub fn parse_judgement<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Judgement, GreedyError<&'a str>> {
        let (input, judgement) = map_opt(is_not(" "), |s| {
            self.judgements
                .iter()
                .enumerate()
                .filter_map(|(i, j)| if s == j { Some(i) } else { None })
                .next()
        })(input)?;
        Ok((input, judgement as u8))
    }

    pub fn format_statement<T: Borrow<[Identifier]> + std::fmt::Debug>(
        &self,
        s: &mut String,
        statement: &Statement<T>,
    ) {
        self.format_judgement(s, statement.judgement);
        s.push(' ');
        self.format_expression(s, &statement.expression);
    }

    pub fn parse_statement<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, OwnedStatement, GreedyError<&'a str>> {
        let (input, judgement) = self.parse_judgement(input)?;
        let (input, _) = char(' ')(input)?;
        let (input, expression) = self.parse_expression(input)?;
        Ok((
            input,
            Statement {
                judgement,
                expression,
            },
        ))
    }

    pub fn format_dvr(&self, s: &mut String, dvr: &DVR) {
        let (a, b) = dvr.variables();
        self.format_variable(s, a);
        s.push_str(" <> ");
        self.format_variable(s, b);
    }

    pub fn parse_dvr<'a>(&self, input: &'a str) -> IResult<&'a str, DVR, GreedyError<&'a str>> {
        let (input, a) = self.parse_variable(input)?;
        let (input, _) = tag(" <> ")(input)?;
        let (input, b) = verify(|input| self.parse_variable(input), |b| *b != a)(input)?;
        Ok((input, DVR::new(a, b).unwrap()))
    }

    pub fn format_theorem(&self, s: &mut String, theorem: &Theorem) {
        let dvrs = theorem.dvrs();
        let assumptions = theorem.assumptions();
        if !dvrs.is_empty() || !assumptions.is_empty() {
            for (i, dvr) in dvrs.iter().enumerate() {
                self.format_dvr(s, dvr);
                if i != dvrs.len() - 1 || !assumptions.is_empty() {
                    s.push_str(", ");
                }
            }
            for (i, assumption) in assumptions.iter().enumerate() {
                self.format_statement(s, assumption);
                if i != assumptions.len() - 1 {
                    s.push_str(", ");
                }
            }
            s.push_str(" => ");
        }
        self.format_statement(s, theorem.conclusion());
    }

    pub fn parse_theorem<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Theorem, GreedyError<&'a str>> {
        alt((
            |input| {
                let (input, dvrs_and_assumptions) = context(
                    "dvrs_and_assumptions",
                    separated_list1(
                        tag(", "),
                        alt((
                            context(
                                "dvr",
                                map(|input| self.parse_dvr(input), |dvr| (Some(dvr), None)),
                            ),
                            context(
                                "assumption",
                                map(
                                    |input| self.parse_statement(input),
                                    |assumption| (None, Some(assumption)),
                                ),
                            ),
                        )),
                    ),
                )(input)?;
                let (input, _) = tag(" => ")(input)?;
                let (input, conclusion) =
                    context("conclusion", |input| self.parse_statement(input))(input)?;
                let (input, _) = eof(input)?;
                let mut dvrs = Vec::new();
                let mut assumptions = Vec::new();
                for (dvr, assumption) in dvrs_and_assumptions {
                    if let Some(dvr) = dvr {
                        dvrs.push(dvr);
                    }
                    if let Some(assumption) = assumption {
                        assumptions.push(assumption);
                    }
                }
                Ok((input, Theorem::new(conclusion, assumptions, dvrs)))
            },
            |input| {
                let (input, conclusion) =
                    context("conclusion", |input| self.parse_statement(input))(input)?;
                let (input, _) = eof(input)?;
                Ok((input, Theorem::new(conclusion, vec![], vec![])))
            },
        ))(input)
    }
}
