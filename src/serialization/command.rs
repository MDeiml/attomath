use std::fmt::Write;

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_till1, take_until},
    character::complete::{char, digit1},
    combinator::{all_consuming, eof, map, map_opt, map_parser, rest},
    error::context,
    sequence::{terminated, tuple},
    IResult,
};

use crate::Theorem;

use super::{
    error::{or_fail, GreedyError},
    Database, DatabaseError, Formatter, Proof,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Command {
    Proof(
        Proof<(Option<String>, Option<usize>)>,
        Option<Theorem>,
        Option<String>,
    ),
    Judgement(String),
    Operator(String, u8),
}

impl Command {
    pub fn apply(self, fmt: &mut Formatter, database: &mut Database) -> Result<(), DatabaseError> {
        match self {
            Command::Proof(proof, theorem, name) => {
                let _theorem = database.add_proof(proof)?;
                if let Some(name) = name {
                    database.add_name(name)?;
                }
                if let Some(theorem) = theorem {
                    database.substitute(theorem)?;
                }
            }
            Command::Judgement(judgement) => {
                fmt.add_judgement(judgement);
            }
            Command::Operator(operator, arity) => {
                fmt.add_operator(operator, arity);
            }
        }
        Ok(())
    }

    pub fn parse<'a>(
        fmt: &Formatter,
        input: &'a str,
    ) -> Result<Self, nom::Err<GreedyError<&'a str>>> {
        let (_, command) = or_fail(all_consuming(alt((
            context(
                "proof",
                alt((
                    context("smp", |input| Self::parse_simplify(&fmt, input)),
                    context("cmb", |input| Self::parse_combine(&fmt, input)),
                    context("axm", |input| Self::parse_axiom(&fmt, input)),
                )),
            ),
            context("jdg", |input| Self::parse_judgement(input)),
            context("opr", |input| Self::parse_operator(input)),
        ))))(input)?;
        Ok(command)
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
        let (input, _) = tag("smp ")(input)?;
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
        let (input, _) = tag("cmb ")(input)?;
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
        let (input, _) = tag("axm { ")(input)?;
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
        let (input, _) = tag("jdg ")(input)?;
        let (input, judgement) = rest(input)?;
        Ok((input, Command::Judgement(judgement.to_owned())))
    }

    fn parse_operator<'a>(input: &'a str) -> IResult<&'a str, Command, GreedyError<&'a str>> {
        let (input, _) = tag("opr ")(input)?;
        let (input, operator) = take_until(" ")(input)?;
        let (input, _) = char(' ')(input)?;
        let (input, arity) = map_opt(digit1, |s: &str| s.parse::<u8>().ok())(input)?;
        Ok((input, Command::Operator(operator.to_owned(), arity)))
    }

    fn serialize_id(&self, s: &mut String, id: &(Option<String>, Option<usize>)) {
        match id {
            (Some(name), Some(index)) => write!(s, "{}.{}", name, index + 1).unwrap(),
            (Some(name), None) => s.push_str(&name),
            (None, Some(index)) => write!(s, "{}", index + 1).unwrap(),
            (None, None) => s.push_str("$"),
        }
    }

    pub fn serialize(&self, s: &mut String, fmt: &Formatter) {
        match self {
            Command::Proof(Proof::Simplify(id, a, b), theorem, name) => {
                s.push_str("smp ");
                self.serialize_id(s, id);
                s.push_str(" (");
                fmt.format_variable(s, *a);
                s.push_str(" ~ ");
                fmt.format_variable(s, *b);
                s.push_str(" )");
                if let Some(theorem) = theorem {
                    s.push_str(" { ");
                    fmt.format_theorem(s, theorem);
                    s.push_str(" }");
                }
                if let Some(name) = name {
                    write!(s, ": {}", name).unwrap();
                }
            }
            Command::Proof(Proof::Combine(id_a, id_b, index), theorem, name) => {
                s.push_str("cmb ");
                self.serialize_id(s, id_a);
                write!(s, "({}) <- ", index + 1).unwrap();
                self.serialize_id(s, id_b);
                if let Some(theorem) = theorem {
                    s.push_str(" { ");
                    fmt.format_theorem(s, theorem);
                    s.push_str(" }");
                }
                if let Some(name) = name {
                    write!(s, ": {}", name).unwrap();
                }
            }
            Command::Proof(Proof::Axiom(theorem), _, name) => {
                s.push_str("axm { ");
                fmt.format_theorem(s, theorem);
                s.push_str(" }");
                if let Some(name) = name {
                    write!(s, ": {}", name).unwrap();
                }
            }
            Command::Judgement(judgement) => {
                write!(s, "jdg {}", judgement).unwrap();
            }
            Command::Operator(operator, arity) => {
                write!(s, "opr {} {}", operator, arity).unwrap();
            }
        }
    }

    pub fn from_formatter<'a>(fmt: &'a Formatter) -> impl 'a + Iterator<Item = Self> {
        fmt.judgements()
            .map(|judgement| Command::Judgement(judgement.to_owned()))
            .chain(
                fmt.operators()
                    .map(|(operator, arity)| Command::Operator(operator.to_owned(), arity)),
            )
    }

    pub fn from_database<'a>(database: &'a Database) -> impl 'a + Iterator<Item = Self> {
        database.proofs().map(|(theorem, proof, name)| {
            let mut should_serialize_theorem = name.is_some();
            if !should_serialize_theorem {
                let mut theorem1 = theorem.clone();
                theorem1.standardize();
                should_serialize_theorem |= &theorem1 != theorem;
            }
            Command::Proof(
                proof.map_id(|(s, n)| (s.map(|s| s.to_owned()), n)),
                if should_serialize_theorem {
                    Some(theorem.clone())
                } else {
                    None
                },
                name.map(|n| n.to_owned()),
            )
        })
    }
}

#[cfg(test)]
mod tests {

    use crate::Identifier;

    use super::*;

    #[derive(Debug)]
    enum Error<'a> {
        ParseError(nom::Err<GreedyError<&'a str>>),
        DatabaseError(DatabaseError),
    }

    impl<'a> From<nom::Err<GreedyError<&'a str>>> for Error<'a> {
        fn from(e: nom::Err<GreedyError<&'a str>>) -> Self {
            Self::ParseError(e)
        }
    }

    impl<'a> From<DatabaseError> for Error<'a> {
        fn from(e: DatabaseError) -> Self {
            Self::DatabaseError(e)
        }
    }

    fn serialize_database(fmt: &Formatter, database: &Database) -> String {
        let mut s = String::new();
        for command in Command::from_formatter(fmt).chain(Command::from_database(database)) {
            command.serialize(&mut s, fmt);
            s.push('\n');
        }
        s
    }

    fn parse_database<'a>(
        fmt: &mut Formatter,
        input: &'a str,
    ) -> Result<Database, (&'a str, Error<'a>)> {
        let mut database = Database::new();
        for line in input.lines() {
            (|| {
                let command = Command::parse(&fmt, line)?;

                command.apply(fmt, &mut database)?;
                Ok(())
            })()
            .map_err(|e| (line, e))?;
        }
        Ok(database)
    }

    #[test]
    fn a_b_c() {
        use crate::{expression::Expression, statement::Statement};
        let mut database = Database::new();

        let a = Statement {
            judgement: 0,
            expression: Expression::from_raw(
                vec![-1, Identifier::MIN, Identifier::MIN].into_boxed_slice(),
            )
            .unwrap(),
        };
        let b = Statement {
            judgement: 0,
            expression: Expression::from_raw(
                vec![-2, Identifier::MIN, Identifier::MIN].into_boxed_slice(),
            )
            .unwrap(),
        };
        let c = Statement {
            judgement: 0,
            expression: Expression::from_raw(
                vec![-3, Identifier::MIN, Identifier::MIN].into_boxed_slice(),
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
        let s = serialize_database(&fmt, &database);
        assert_eq!(
            s,
            r#"jdg |-
opr A 0
opr B 0
opr C 0
axm { |- A }
axm { |- B }: b
axm { |- A, |- B => |- C }: abc
cmb abc(1) <- b.1
cmb $(1) <- b { |- C }: c
"#
        );

        let mut fmt1 = Formatter::new();
        let database1 = parse_database(&mut fmt1, &s).unwrap();
        assert_eq!(database1, database);
        assert_eq!(fmt1, fmt);
    }

    #[test]
    fn id() {
        let s = r#"jdg wff
jdg |-
opr -> 2
opr -. 1
axm { wff a => wff (-. a) }: wn
axm { wff a, wff b => wff (a -> b) }: wi
axm { wff a, wff b, |- a, |- (a -> b) => |- b }: ax-mp
axm { wff a, wff b => |- (a -> (b -> a)) }: ax-1
axm { wff a, wff b, wff c => |- ((a -> (b -> c)) -> ((a -> b) -> (a -> c))) }: ax-2
axm { wff a, wff b => |- (((-. a) -> (-. b)) -> (b -> a)) }: ax-3
cmb ax-mp(1) <- wi
cmb $(3) <- wi
cmb $(1) <- wi
cmb $(1) <- wi
cmb $(3) <- wi
cmb $(9) <- ax-2 { wff a, wff b, wff c, |- (a -> (b -> c)) => |- ((a -> b) -> (a -> c)) }: a2i
cmb ax-mp(1) <- wi
cmb $(1) <- wi
cmb $(6) <- a2i { wff a, wff b, wff c, |- (a -> b), |- (a -> (b -> c)) => |- (a -> c) }: mpd
smp ax-1 (a ~ b)
cmb mpd(2) <- wi
cmb $(5) <- 1
cmb ax-1(2) <- wi
smp $ (a ~ b)
smp $ (a ~ b)
smp $ (a ~ b)
cmb 3(3) <- $ { wff a => |- (a -> a) }: id
"#;
        let mut fmt = Formatter::new();
        match parse_database(&mut fmt, s) {
            Err((line, e)) => {
                eprintln!("In line:\n\t{}", line);
                match e {
                    Error::DatabaseError(DatabaseError::TheoremMismatch(t1, t2)) => {
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
