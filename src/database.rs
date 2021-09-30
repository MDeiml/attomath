use std::collections::HashMap;
use std::fmt::Write;

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_till1, take_until},
    character::complete::{char, digit1},
    combinator::{eof, map, map_opt, map_parser, rest},
    error::context,
    sequence::{terminated, tuple},
    IResult,
};

use crate::{
    error::{or_fail, GreedyError, ProofError},
    expression::SingleSubstitution,
    formatter::Formatter,
    Identifier, Theorem,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Database {
    names: HashMap<String, (usize, usize)>,
    theorems: Vec<(Theorem, Proof<usize>, Option<String>)>,
    last_name: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Proof<K> {
    Simplify(K, Identifier, Identifier),
    Combine(K, K, usize),
    Axiom(Theorem),
}

#[derive(Debug, PartialEq, Eq)]
enum Command {
    Proof(
        Proof<(Option<String>, Option<usize>)>,
        Option<Theorem>,
        Option<String>,
    ),
    Judgement(String),
    Operator(String, u8),
}

#[derive(Debug)]
pub enum DatabaseError {
    /// Error produced when trying to use a nonexistent theorem id (see
    /// [`Database`](../database/struct.Database.html)
    TheoremNotFound(Option<String>, Option<usize>),
    /// Error produced when trying to insert using a already used theorem id (see
    /// [`Database`](../database/struct.Database.html)
    NameCollision(String),
    TheoremMismatch(Theorem, Theorem),
    ProofError(ProofError),
    ParseError,
}

impl From<ProofError> for DatabaseError {
    fn from(e: ProofError) -> Self {
        Self::ProofError(e)
    }
}

impl<'a> From<nom::Err<GreedyError<&'a str>>> for DatabaseError {
    fn from(_error: nom::Err<GreedyError<&'a str>>) -> Self {
        // TODO
        Self::ParseError
    }
}

impl Database {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            theorems: Vec::new(),
            last_name: 0,
        }
    }

    fn get_index(&self, name: Option<&str>, index: Option<usize>) -> Result<usize, DatabaseError> {
        let (start, end) = match name {
            Some(name) => *self
                .names
                .get(name)
                .ok_or(DatabaseError::TheoremNotFound(Some(name.to_owned()), index))?,
            None => (self.last_name, self.theorems.len()),
        };
        match index {
            Some(i) => {
                if start + i < end {
                    Ok(start + i)
                } else {
                    Err(DatabaseError::TheoremNotFound(
                        name.map(|s| s.to_owned()),
                        index,
                    ))
                }
            }
            None => {
                if start == end {
                    Err(DatabaseError::TheoremNotFound(
                        name.map(|s| s.to_owned()),
                        index,
                    ))
                } else {
                    Ok(end - 1)
                }
            }
        }
    }

    pub fn get(&self, name: Option<&str>, index: Option<usize>) -> Result<&Theorem, DatabaseError> {
        Ok(&self.theorems[self.get_index(name, index)?].0)
    }

    pub fn add_name(&mut self, name: String) -> Result<(), DatabaseError> {
        if self.theorems.is_empty() {
            return Err(DatabaseError::TheoremNotFound(None, Some(0)));
        }
        let index = self.theorems.len() - 1;
        if self.theorems[index].2.is_some() {
            return Err(DatabaseError::TheoremNotFound(None, None));
        }
        match self.names.entry(name.clone()) {
            std::collections::hash_map::Entry::Occupied(_) => {
                Err(DatabaseError::NameCollision(name))
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                &entry.insert((self.last_name, index + 1));
                self.last_name = index + 1;
                self.theorems[index].2 = Some(name.to_owned());
                Ok(())
            }
        }
    }

    pub fn add_proof<'a>(
        &'a mut self,
        proof: Proof<(Option<String>, Option<usize>)>,
    ) -> Result<&'a Theorem, DatabaseError> {
        let (new_theorem, proof) = match proof {
            Proof::Simplify(id, a, b) => {
                let index = self.get_index(id.0.as_deref(), id.1)?;
                let theorem = &self.theorems[index].0;
                let mut new_theorem = theorem.substitute(&SingleSubstitution::new(a, b))?;
                new_theorem.standardize();
                (new_theorem, Proof::Simplify(index, a, b))
            }
            Proof::Combine(id_a, id_b, index) => {
                let index_a = self.get_index(id_a.0.as_deref(), id_a.1)?;
                let theorem_a = &self.theorems[index_a].0;
                let index_b = self.get_index(id_b.0.as_deref(), id_b.1)?;
                let theorem_b = &self.theorems[index_b].0;
                let mut new_theorem = theorem_a.combine(&theorem_b, index)?;
                new_theorem.standardize();
                (new_theorem, Proof::Combine(index_a, index_b, index))
            }
            Proof::Axiom(theorem) => (theorem.clone(), Proof::Axiom(theorem)),
        };
        self.theorems.push((new_theorem, proof, None));
        Ok(&self.theorems.last().unwrap().0)
    }

    pub fn substitute(&mut self, theorem: Theorem) -> Result<(), DatabaseError> {
        let last = &mut self
            .theorems
            .last_mut()
            .ok_or(DatabaseError::TheoremNotFound(None, None))?
            .0;
        let mut theorem_standardized = theorem.clone();
        theorem_standardized.standardize();
        if last == &theorem_standardized {
            *last = theorem;
            Ok(())
        } else {
            Err(DatabaseError::TheoremMismatch(theorem, last.clone()))
        }
    }

    fn reverse_id(&self, id: usize, current_id: usize) -> (Option<&str>, Option<usize>) {
        if let Some(name) = &self.theorems[id].2 {
            (Some(name), None)
        } else if id == current_id - 1 {
            (None, None)
        } else if id >= self.last_name {
            (None, Some(id - self.last_name))
        } else {
            let name = self.theorems[id..]
                .iter()
                .filter_map(|x| x.2.as_ref())
                .next()
                .unwrap();
            let (start, end) = self.names[name];
            if end >= current_id {
                (None, Some(id - start))
            } else {
                (Some(name), Some(id - start))
            }
        }
    }

    fn serialize_id(&self, s: &mut String, id: usize, current_id: usize) {
        match self.reverse_id(id, current_id) {
            (Some(name), Some(index)) => write!(s, "{}.{}", name, index + 1).unwrap(),
            (Some(name), None) => s.push_str(name),
            (None, Some(index)) => write!(s, "{}", index + 1).unwrap(),
            (None, None) => s.push_str("$"),
        }
    }

    pub fn serialize(&self, fmt: &Formatter) -> String {
        let mut s = String::new();
        for (current_id, (theorem, proof, name)) in self.theorems.iter().enumerate() {
            match proof {
                Proof::Simplify(id, a, b) => {
                    s.push_str("simplify ");
                    self.serialize_id(&mut s, *id, current_id);
                    s.push_str(" (");
                    fmt.format_variable(&mut s, *a);
                    s.push_str(" ~ ");
                    fmt.format_variable(&mut s, *b);
                    s.push_str(" )");
                    if let Some(name) = name {
                        s.push_str(" { ");
                        fmt.format_theorem(&mut s, theorem);
                        write!(s, " }}: {}", name).unwrap();
                    } else {
                        let mut theorem_standardized = theorem.clone();
                        theorem_standardized.standardize();
                        if &theorem_standardized != theorem {
                            s.push_str(" { ");
                            fmt.format_theorem(&mut s, theorem);
                            s.push_str(" }");
                        }
                    }
                    s.push('\n');
                }
                Proof::Combine(id_a, id_b, index) => {
                    s.push_str("combine ");
                    self.serialize_id(&mut s, *id_a, current_id);
                    write!(s, "({}) <- ", index + 1).unwrap();
                    self.serialize_id(&mut s, *id_b, current_id);
                    if let Some(name) = name {
                        s.push_str(" { ");
                        fmt.format_theorem(&mut s, theorem);
                        write!(s, " }}: {}", name).unwrap();
                    } else {
                        let mut theorem_standardized = theorem.clone();
                        theorem_standardized.standardize();
                        if &theorem_standardized != theorem {
                            s.push_str(" { ");
                            fmt.format_theorem(&mut s, theorem);
                            s.push_str(" }");
                        }
                    }
                    s.push('\n');
                }
                Proof::Axiom(_) => {
                    s.push_str("axiom { ");
                    fmt.format_theorem(&mut s, theorem);
                    s.push_str(" }");
                    if let Some(name) = name {
                        write!(s, ": {}", name).unwrap();
                    }
                    s.push('\n');
                }
            }
        }
        s
    }

    fn parse_id(input: &str) -> IResult<&str, (Option<String>, Option<usize>), GreedyError<&str>> {
        alt((
            terminated(map(char('$'), |_| (None, None)), eof),
            terminated(
                map_opt(digit1, |s: &str| {
                    Some((
                        None,
                        Some(s.parse::<usize>().ok().and_then(|i| {
                            if i == 0 {
                                None
                            } else {
                                Some(i - 1)
                            }
                        })?),
                    ))
                }),
                eof,
            ),
            terminated(
                map_opt(
                    tuple((take_till1(|c| c == '.' || c == ' '), char('.'), digit1)),
                    |(name, _, s): (&str, char, &str)| -> Option<(Option<String>, Option<usize>)> {
                        Some((
                            Some(name.to_owned()),
                            Some(s.parse::<usize>().ok().and_then(|i| {
                                if i == 0 {
                                    None
                                } else {
                                    Some(i - 1)
                                }
                            })?),
                        ))
                    },
                ),
                eof,
            ),
            terminated(
                map(take_till1(|c| c == '.' || c == ' '), |name: &str| {
                    (Some(name.to_owned()), None)
                }),
                eof,
            ),
        ))(input)
    }

    fn parse_simplify<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Command, GreedyError<&'a str>> {
        let (input, _) = tag("simplify ")(input)?;
        or_fail(|input| {
            let (input, id) = map_parser(is_not(" "), Self::parse_id)(input)?;
            let (input, _) = tag(" (")(input)?;
            let (input, a) = fmt.parse_variable(input)?;
            let (input, _) = tag(" ~ ")(input)?;
            let (input, b) = fmt.parse_variable(input)?;
            let (input, _) = tag(")")(input)?;
            let (input, (theorem, name)) = alt((
                map(eof, |_| (None, None)),
                map(
                    tuple((
                        tag(" { "),
                        map_parser(take_until(" }"), |input| fmt.parse_theorem(input)),
                        tag(" }"),
                        alt((
                            map(eof, |_| None),
                            map(tuple((tag(": "), rest)), |(_, name): (&str, &str)| {
                                Some(name.to_owned())
                            }),
                        )),
                    )),
                    |(_, theorem, _, name)| (Some(theorem), name),
                ),
                map(tuple((tag(": "), rest)), |(_, name): (&str, &str)| {
                    (None, Some(name.to_owned()))
                }),
            ))(input)?;
            Ok((
                input,
                Command::Proof(Proof::Simplify(id, a, b), theorem, name),
            ))
        })(input)
    }

    fn parse_combine<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Command, GreedyError<&'a str>> {
        let (input, _) = tag("combine ")(input)?;
        or_fail(|input| {
            let (input, id_a) = map_parser(is_not("("), Self::parse_id)(input)?;
            let (input, _) = tag("(")(input)?;
            let (input, index) = map_opt(digit1, |s: &str| {
                s.parse::<usize>().ok().filter(|i| *i != 0)
            })(input)?;
            let (input, _) = tag(") <- ")(input)?;
            let (input, id_b) = map_parser(is_not(" "), Self::parse_id)(input)?;
            let (input, (theorem, name)) = alt((
                map(eof, |_| (None, None)),
                map(
                    tuple((
                        tag(" { "),
                        map_parser(take_until(" }"), |input| fmt.parse_theorem(input)),
                        tag(" }"),
                        alt((
                            map(eof, |_| None),
                            map(tuple((tag(": "), rest)), |(_, name): (&str, &str)| {
                                Some(name.to_owned())
                            }),
                        )),
                    )),
                    |(_, theorem, _, name)| (Some(theorem), name),
                ),
                map(tuple((tag(": "), rest)), |(_, name): (&str, &str)| {
                    (None, Some(name.to_owned()))
                }),
            ))(input)?;
            Ok((
                input,
                Command::Proof(Proof::Combine(id_a, id_b, index - 1), theorem, name),
            ))
        })(input)
    }

    fn parse_axiom<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> IResult<&'a str, Command, GreedyError<&'a str>> {
        let (input, _) = tag("axiom { ")(input)?;
        or_fail(|input| {
            let (input, theorem) =
                map_parser(take_until(" }"), |input| fmt.parse_theorem(input))(input)?;
            let (input, _) = tag(" }")(input)?;
            let (input, name) = alt((
                map(eof, |_| None),
                map(tuple((tag(": "), rest)), |(_, name): (&str, &str)| {
                    Some(name.to_owned())
                }),
            ))(input)?;
            Ok((
                input,
                Command::Proof(Proof::Axiom(theorem.clone()), None, name),
            ))
        })(input)
    }

    fn parse_judgement<'a>(input: &'a str) -> IResult<&'a str, Command, GreedyError<&'a str>> {
        let (input, _) = tag("judgement ")(input)?;
        let (input, judgement) = rest(input)?;
        Ok((input, Command::Judgement(judgement.to_owned())))
    }

    fn parse_operator<'a>(input: &'a str) -> IResult<&'a str, Command, GreedyError<&'a str>> {
        let (input, _) = tag("operator ")(input)?;
        let (input, operator) = take_until(" ")(input)?;
        let (input, _) = char(' ')(input)?;
        let (input, arity) = map_opt(digit1, |s: &str| s.parse::<u8>().ok())(input)?;
        Ok((input, Command::Operator(operator.to_owned(), arity)))
    }

    pub fn parse_database<'a>(
        fmt: &mut Formatter,
        input: &'a str,
    ) -> Result<Self, (&'a str, DatabaseError)> {
        let mut database = Self::new();
        for line in input.lines() {
            (|| {
                let res: Result<_, nom::Err<GreedyError<_>>> = or_fail(alt((
                    context(
                        "proof",
                        alt((
                            context("simplify", |input| Self::parse_simplify(&fmt, input)),
                            context("combine", |input| Self::parse_combine(&fmt, input)),
                            context("axiom", |input| Self::parse_axiom(&fmt, input)),
                        )),
                    ),
                    context("judgement", |input| Self::parse_judgement(input)),
                    context("operator", |input| Self::parse_operator(input)),
                )))(line);
                let (input, command) = res?;
                if !input.is_empty() {
                    return Err(DatabaseError::ParseError);
                }

                match command {
                    Command::Proof(proof, theorem, name) => {
                        let _theorem1 = database.add_proof(proof)?;
                        if let Some(theorem) = theorem {
                            database.substitute(theorem)?;
                        }
                        if let Some(name) = name {
                            database.add_name(name)?;
                        }
                    }
                    Command::Judgement(judgement) => fmt.add_judgement(judgement),
                    Command::Operator(operator, arity) => fmt.add_operator(operator, arity),
                }
                Ok(())
            })()
            .map_err(|e| (line, e))?;
        }
        Ok(database)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    #[test]
    fn a_b_c() {
        use crate::{expression::Expression, statement::Statement};
        let mut database = Database::new();

        let a = Statement {
            judgement: 0,
            expression: Expression::from_raw(
                vec![-2, Identifier::MIN, Identifier::MIN].into_boxed_slice(),
            )
            .unwrap(),
        };
        let b = Statement {
            judgement: 0,
            expression: Expression::from_raw(
                vec![-3, Identifier::MIN, Identifier::MIN].into_boxed_slice(),
            )
            .unwrap(),
        };
        let c = Statement {
            judgement: 0,
            expression: Expression::from_raw(
                vec![-4, Identifier::MIN, Identifier::MIN].into_boxed_slice(),
            )
            .unwrap(),
        };

        database
            .add_proof(Proof::Axiom(Theorem::new(a.clone(), vec![], vec![])))
            .unwrap();

        database
            .add_proof(Proof::Axiom(Theorem::new(b.clone(), vec![], vec![])))
            .unwrap();
        database.add_name("b".to_owned()).unwrap();

        database
            .add_proof(Proof::Axiom(Theorem::new(c.clone(), vec![a, b], vec![])))
            .unwrap();
        database.add_name("abc".to_owned()).unwrap();

        database
            .add_proof(Proof::Combine(
                (Some("abc".to_owned()), None),
                (Some("b".to_owned()), Some(0)),
                0,
            ))
            .unwrap();
        database
            .add_proof(Proof::Combine(
                (None, None),
                (Some("b".to_owned()), None),
                0,
            ))
            .unwrap();
        database.add_name("c".to_owned()).unwrap();

        let theorem = database.get(Some("c"), None).unwrap();
        assert_eq!(theorem, &Theorem::new(c, vec![], vec![]));

        let mut fmt = Formatter::new();
        fmt.add_operator("A".to_owned(), 0);
        fmt.add_operator("B".to_owned(), 0);
        fmt.add_operator("C".to_owned(), 0);
        fmt.add_judgement("|-".to_owned());
        let s = database.serialize(&fmt);
        assert_eq!(
            s,
            r#"axiom { |- A }
axiom { |- B }: b
axiom { |- A, |- B => |- C }: abc
combine abc(1) <- b.1
combine $(1) <- b { |- C }: c
"#
        );

        let database1 = Database::parse_database(&mut fmt, &s).unwrap();
        assert_eq!(database1, database);
    }

    #[test]
    fn id() {
        let s = r#"judgement wff
judgement |-
operator -> 2
operator -. 1
axiom { wff a => wff (-. a) }: wn
axiom { wff a, wff b => wff (a -> b) }: wi
axiom { wff a, wff b, |- a, |- (a -> b) => |- b }: ax-mp
axiom { wff a, wff b => |- (a -> (b -> a)) }: ax-1
axiom { wff a, wff b, wff c => |- ((a -> (b -> c)) -> ((a -> b) -> (a -> c))) }: ax-2
axiom { wff a, wff b => |- (((-. a) -> (-. b)) -> (b -> a)) }: ax-3
combine ax-mp(1) <- wi
combine $(3) <- wi
combine $(1) <- wi
combine $(1) <- wi
combine $(3) <- wi
combine $(9) <- ax-2 { wff a, wff b, wff c, |- (a -> (b -> c)) => |- ((a -> b) -> (a -> c)) }: a2i
combine ax-mp(1) <- wi
combine $(1) <- wi
combine $(6) <- a2i { wff a, wff b, wff c, |- (a -> b), |- (a -> (b -> c)) => |- (a -> c) }: mpd
simplify ax-1 (a ~ b)
combine mpd(2) <- wi
combine $(5) <- 1
combine ax-1(2) <- wi
simplify $ (a ~ b)
simplify $ (a ~ b)
simplify $ (a ~ b)
combine 3(3) <- $ { wff a => |- (a -> a) }: id
"#;
        let mut fmt = Formatter::new();
        match Database::parse_database(&mut fmt, s) {
            Err((line, e)) => {
                eprintln!("In line:\n\t{}", line);
                match e {
                    DatabaseError::TheoremMismatch(t1, t2) => {
                        let mut s1 = String::new();
                        fmt.format_theorem(&mut s1, &t1);
                        let mut s2 = String::new();
                        fmt.format_theorem(&mut s2, &t2);
                        panic!("TheoremMismatch:\n{}\n{}", s1, s2);
                    }
                    e => {
                        panic!("{:?}", e);
                    }
                }
            }
            _ => (),
        }
    }
}
