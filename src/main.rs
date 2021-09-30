use std::{
    fs::File,
    io::{BufRead, BufReader},
};

use attomath::{
    command::Command,
    database::{Database, Proof},
    formatter::Formatter,
    Expression,
};

// fn parse_database<'a>(
//     fmt: &mut Formatter,
//     input: &'a str,
// ) -> Result<Database, (&'a str, Error<'a>)> {
//     let mut database = Database::new();
//     for line in input.lines() {
//         (|| {
//             let command = Command::parse(&fmt, line)?;

//             command.apply(fmt, &mut database)?;
//             Ok(())
//         })()
//         .map_err(|e| (line, e))?;
//     }
//     Ok(database)
// }

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let mut fmt = Formatter::new();
    let mut database = Database::new();

    let file = File::open(filename).unwrap();
    for (line_number, line) in BufReader::new(file).lines().enumerate() {
        let line = line.unwrap();
        let command = match Command::parse(&fmt, &line) {
            Ok(command) => command,
            Err(err) => {
                eprintln!(
                    "Syntax error in line {}: {:?}\n\t{}",
                    line_number, err, line
                );
                return;
            }
        };
        match command.clone().apply(&mut fmt, &mut database) {
            Ok(_) => (),
            Err(err) => {
                eprint!("Error in line {}: ", line_number);
                match err {
                    attomath::database::DatabaseError::TheoremNotFound(name, id) => {
                        match (name, id) {
                            (Some(name), Some(id)) => eprint!("theorem {}.{} not found", name, id),
                            (Some(name), None) => eprintln!("theorem {} not found", name),
                            (None, Some(id)) => eprint!("theorem {} not found", id),
                            (None, None) => eprintln!("theorem $ not found"),
                        }
                    }
                    attomath::database::DatabaseError::NameCollision(name) => {
                        eprintln!("{} already defined", name)
                    }
                    attomath::database::DatabaseError::TheoremMismatch(theorem_a, theorem_b) => {
                        eprintln!("theorem mismatch");
                        let mut sa = String::new();
                        fmt.format_theorem(&mut sa, &theorem_a);
                        let mut sb = String::new();
                        fmt.format_theorem(&mut sb, &theorem_b);
                        eprintln!("expected: {}", sb);
                        eprintln!("   found: {}", sa);
                    }
                    attomath::database::DatabaseError::ProofError(err) => {
                        let (id_a, id_b, index) = match command {
                            Command::Proof(Proof::Combine(id_a, id_b, index), _, _) => {
                                (id_a, id_b, index)
                            }
                            _ => unreachable!(),
                        };
                        let theorem_a = database.get(id_a.0.as_deref(), id_a.1).unwrap();
                        let theorem_b = database.get(id_b.0.as_deref(), id_b.1).unwrap();
                        let mut sa = String::new();
                        fmt.format_theorem(&mut sa, &theorem_a);
                        let mut sb = String::new();
                        fmt.format_theorem(&mut sb, &theorem_b);
                        let mut ss = String::new();
                        fmt.format_statement(&mut ss, &theorem_a.assumptions()[index]);
                        eprintln!(
                            "proof error combining\n{}\ninto the argument {} of\n{}",
                            sb, ss, sa
                        );
                        match err {
                            attomath::error::ProofError::OperatorMismatch(op_a, op_b) => eprintln!(
                                "operator mismatch: expected {} found {}",
                                fmt.operators().nth((-op_b) as usize - 1).unwrap().0,
                                fmt.operators().nth((-op_a) as usize - 1).unwrap().0,
                            ),
                            attomath::error::ProofError::VariableMismatch(var, sub_a, sub_b) => {
                                let mut sv = String::new();
                                fmt.format_variable(&mut sv, var);
                                let mut sa = String::new();
                                fmt.format_expression(
                                    &mut sa,
                                    &Expression::from_raw(sub_b).unwrap(),
                                );
                                let mut sb = String::new();
                                fmt.format_expression(
                                    &mut sb,
                                    &Expression::from_raw(sub_a).unwrap(),
                                );
                                eprintln!(
                                    "variable {} is substituted for both {} and {}",
                                    sv, sa, sb
                                )
                            }
                            attomath::error::ProofError::JudgementMismatch(ja, jb) => eprintln!(
                                "judgement mismatch: expected {} found {}",
                                fmt.judgements().nth(jb as usize).unwrap(),
                                fmt.judgements().nth(ja as usize).unwrap(),
                            ),
                            attomath::error::ProofError::DVRError(_) => {
                                eprintln!("Distinct variable relation violated")
                            }
                        };
                    }
                };
                eprintln!("\t{}", line);
                return;
            }
        }
    }
}
