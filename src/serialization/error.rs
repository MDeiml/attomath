use std::fmt::Display;

use nom::{
    error::{ContextError, ErrorKind, ParseError},
    IResult, Parser,
};

#[derive(Debug)]
pub struct GreedyError<I>(Vec<(I, GreedyErrorKind)>);

#[derive(Debug)]
enum GreedyErrorKind {
    Context(&'static str),
    Nom(ErrorKind),
    Char(char),
}

pub trait Length {
    fn length(&self) -> usize;
}

impl Length for &str {
    fn length(&self) -> usize {
        self.len()
    }
}

impl Display for GreedyError<&str> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (input, error) in self.0.iter() {
            writeln!(f, "{:?} {}", error, &input[0..20])?;
        }
        Ok(())
    }
}

impl<I> ParseError<I> for GreedyError<I>
where
    I: Length,
{
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        Self(vec![(input, GreedyErrorKind::Nom(kind))])
    }

    fn append(input: I, kind: ErrorKind, mut other: Self) -> Self {
        other.0.push((input, GreedyErrorKind::Nom(kind)));
        other
    }

    fn from_char(input: I, c: char) -> Self {
        Self(vec![(input, GreedyErrorKind::Char(c))])
    }

    fn or(self, other: Self) -> Self {
        if self.0[0].0.length() < other.0[0].0.length() {
            self
        } else {
            other
        }
    }
}

impl<I> ContextError<I> for GreedyError<I> {
    fn add_context(input: I, ctx: &'static str, mut other: Self) -> Self {
        other.0.push((input, GreedyErrorKind::Context(ctx)));
        other
    }
}

pub fn or_fail<I, O, E: ParseError<I>, F>(mut f: F) -> impl FnMut(I) -> IResult<I, O, E>
where
    F: Parser<I, O, E>,
{
    move |input| {
        f.parse(input).map_err(|error| match error {
            nom::Err::Error(e) => nom::Err::Failure(e),
            e => e,
        })
    }
}
