use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while1},
    combinator::{eof, map, verify},
    error::context,
    multi::{many0, many1, many_till},
    sequence::{delimited, tuple},
    IResult,
};

use crate::{database::Database, error::GreedyError};

#[derive(Debug)]
enum GlobalStatement<'a> {
    FileInclusion { filename: &'a str },
    Constant { name: &'a str },
    Statement { statement: Statement<'a> },
}

#[derive(Debug)]
enum Statement<'a> {
    Scope {
        statements: Vec<Statement<'a>>,
    },
    Variable {
        name: &'a str,
    },
    Type {
        label: &'a str,
        typecode: &'a str,
        variable: &'a str,
    },
    Hypothethis {
        label: &'a str,
        typecode: &'a str,
        expression: Vec<&'a str>,
    },
    DVR {
        a: &'a str,
        b: &'a str,
    },
    Axiom {
        label: &'a str,
        typecode: &'a str,
        expression: Vec<&'a str>,
    },
    Assertion {
        label: &'a str,
        typecode: &'a str,
        expression: Vec<&'a str>,
        proof: MetamathProof<'a>,
    },
}

#[derive(Debug)]
enum MetamathProof<'a> {
    Uncompressed(Vec<&'a str>),
    Compressed(Vec<&'a str>, &'a str),
}

fn metamath_whitespace(c: char) -> bool {
    c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == ' '
}

fn metamath_mathsymbol(c: char) -> bool {
    c >= '!' && c <= '~' && c != '$'
}

fn metamath_label(c: char) -> bool {
    (c >= 'a' && c <= 'z')
        || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9')
        || c == '-'
        || c == '.'
        || c == '_'
}

fn whitespace(input: &str) -> IResult<&str, (), GreedyError<&str>> {
    let (input, _) = context("whitespace", take_while1(metamath_whitespace))(input)?;
    Ok((input, ()))
}

fn mathsymbol(input: &str) -> IResult<&str, &str, GreedyError<&str>> {
    context("mathsymbol", take_while1(metamath_mathsymbol))(input)
}

fn label(input: &str) -> IResult<&str, &str, GreedyError<&str>> {
    context("label", take_while1(metamath_label))(input)
}

fn comment(input: &str) -> IResult<&str, (), GreedyError<&str>> {
    let (input, _comment) = verify(
        delimited(tag("$("), take_until("$)"), tag("$)")),
        |comment: &str| !comment.contains("$("),
    )(input)?;
    Ok((input, ()))
}

fn file_inclusion(input: &str) -> IResult<&str, GlobalStatement, GreedyError<&str>> {
    let (input, filename) = verify(
        delimited(tag("$["), take_until("$]"), tag("$]")),
        |filename: &str| !filename.contains("$"),
    )(input)?;
    Ok((input, GlobalStatement::FileInclusion { filename }))
}

fn constant(input: &str) -> IResult<&str, Vec<GlobalStatement>, GreedyError<&str>> {
    let (input, _) = tag("$c")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, statements) = many1(map(tuple((mathsymbol, whitespace)), |(name, _)| {
        GlobalStatement::Constant { name }
    }))(input)?;
    let (input, _) = tag("$.")(input)?;
    Ok((input, statements))
}

fn scope(input: &str) -> IResult<&str, Statement, GreedyError<&str>> {
    let (input, _) = tag("${")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, (statementses, _)) =
        many_till(map(tuple((statement, whitespace)), |(s, _)| s), tag("$}"))(input)?;
    Ok((
        input,
        Statement::Scope {
            statements: statementses.into_iter().flatten().collect(),
        },
    ))
}

fn variable(input: &str) -> IResult<&str, Vec<Statement>, GreedyError<&str>> {
    let (input, _) = tag("$v")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, statements) = many1(map(tuple((mathsymbol, whitespace)), |(name, _)| {
        Statement::Variable { name }
    }))(input)?;
    let (input, _) = tag("$.")(input)?;
    Ok((input, statements))
}

fn parse_type(input: &str) -> IResult<&str, Statement, GreedyError<&str>> {
    let (input, l) = label(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("$f")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, typecode) = mathsymbol(input)?;
    let (input, _) = whitespace(input)?;
    let (input, variable) = mathsymbol(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("$.")(input)?;
    Ok((
        input,
        Statement::Type {
            label: l,
            typecode,
            variable,
        },
    ))
}

fn hypothethis(input: &str) -> IResult<&str, Statement, GreedyError<&str>> {
    let (input, l) = label(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("$e")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, typecode) = mathsymbol(input)?;
    let (input, _) = whitespace(input)?;
    let (input, expression) = many0(map(tuple((mathsymbol, whitespace)), |(s, _)| s))(input)?;
    let (input, _) = tag("$.")(input)?;
    Ok((
        input,
        Statement::Hypothethis {
            label: l,
            typecode,
            expression,
        },
    ))
}

fn dvr(input: &str) -> IResult<&str, Vec<Statement>, GreedyError<&str>> {
    let (input, _) = tag("$d")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, variables) = many1(map(tuple((mathsymbol, whitespace)), |(s, _)| s))(input)?;
    let (input, _) = tag("$.")(input)?;
    let mut dvrs = Vec::new();
    for i in 0..variables.len() {
        for j in i + 1..variables.len() {
            dvrs.push(Statement::DVR {
                a: variables[i],
                b: variables[j],
            });
        }
    }
    Ok((input, dvrs))
}

fn axiom(input: &str) -> IResult<&str, Statement, GreedyError<&str>> {
    let (input, l) = label(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("$a")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, typecode) = mathsymbol(input)?;
    let (input, _) = whitespace(input)?;
    let (input, expression) = many0(map(tuple((mathsymbol, whitespace)), |(s, _)| s))(input)?;
    let (input, _) = tag("$.")(input)?;
    Ok((
        input,
        Statement::Axiom {
            label: l,
            typecode,
            expression,
        },
    ))
}

fn compressed_proof(input: &str) -> IResult<&str, MetamathProof, GreedyError<&str>> {
    let (input, _) = tag("(")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, labels) = many0(map(tuple((label, whitespace)), |(s, _)| s))(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, proof) = take_while1(|c| (c >= 'A' && c <= 'Z') || metamath_whitespace(c))(input)?;
    Ok((input, MetamathProof::Compressed(labels, proof)))
}

fn assertion(input: &str) -> IResult<&str, Statement, GreedyError<&str>> {
    let (input, l) = label(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("$p")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, typecode) = mathsymbol(input)?;
    let (input, _) = whitespace(input)?;
    let (input, expression) = many0(map(tuple((mathsymbol, whitespace)), |(s, _)| s))(input)?;
    let (input, _) = tag("$=")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, proof) = alt((
        context("compressed_proof", compressed_proof),
        context(
            "normal_proof",
            map(many0(map(tuple((label, whitespace)), |(s, _)| s)), |p| {
                MetamathProof::Uncompressed(p)
            }),
        ),
    ))(input)?;
    let (input, _) = tag("$.")(input)?;
    Ok((
        input,
        Statement::Assertion {
            label: l,
            typecode,
            expression,
            proof,
        },
    ))
}

fn statement(input: &str) -> IResult<&str, Vec<Statement>, GreedyError<&str>> {
    alt((
        context("comment", map(comment, |_| vec![])),
        context("variable", variable),
        context("type", map(parse_type, |s| vec![s])),
        context("dvr", dvr),
        context("axiom", map(axiom, |s| vec![s])),
        context("assertion", map(assertion, |s| vec![s])),
        context("hypothethis", map(hypothethis, |s| vec![s])),
        context("scope", map(scope, |s| vec![s])),
    ))(input)
}

fn global_statement(input: &str) -> IResult<&str, Vec<GlobalStatement>, GreedyError<&str>> {
    alt((
        context("file_inclusion", map(file_inclusion, |x| vec![x])),
        context("constant", constant),
        map(statement, |ss| {
            ss.into_iter()
                .map(|s| GlobalStatement::Statement { statement: s })
                .collect()
        }),
    ))(input)
}

fn parse_file<'a>(input: &'a str) -> IResult<&'a str, Vec<GlobalStatement<'a>>, GreedyError<&str>> {
    let (input, _) = whitespace(input)?;
    let (input, (statementses, _)) =
        many_till(map(tuple((global_statement, whitespace)), |(s, _)| s), eof)(input)?;
    Ok((input, statementses.into_iter().flatten().collect()))
}

pub fn load_metamath(filename: &str) -> Database {
    let file = std::fs::read_to_string(filename).unwrap(); // TODO
    let res = parse_file(&file);
    if let Err(nom::Err::Error(e)) = res {
        panic!("{}", e);
    }
    Database::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_set_mm() {
        load_metamath("metamath/set.mm");
    }
}
