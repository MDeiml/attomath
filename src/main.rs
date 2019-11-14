#[macro_use]
extern crate diesel;
extern crate bincode;
#[macro_use]
extern crate diesel_migrations;
extern crate nom;

pub mod auto;
pub mod dvr;
pub mod error;
pub mod expression;
pub mod formatter;
pub mod schema;
pub mod statement;
pub mod substitution;
pub mod theorem;
pub mod types;

use auto::*;
use diesel::prelude::*;
use diesel::sqlite::SqliteConnection;
use formatter::Formatter;
use nom::combinator::all_consuming;
use theorem::{DBTheorem, Theorem};

fn parse_theorem<'a>(fmt: &Formatter, input: &'a str) -> Theorem {
    all_consuming(|s| Theorem::parse(fmt, s))(input).unwrap().1
}

embed_migrations!("migrations");

fn main() {
    let database_url = ":memory:";
    let conn = SqliteConnection::establish(database_url).unwrap();
    embedded_migrations::run(&conn).unwrap();

    let fmt = Formatter {
        operators: vec![("->", true), ("-.", false)],
        judgements: vec!["wff", "|-"],
    };

    let wff2 = parse_theorem(&fmt, "wff x0, wff x1 => wff (x0 -> x1)");
    let ax1 = parse_theorem(&fmt, "wff x0, wff x1 => |- (x0 -> (x1 -> x0))");
    let ax2 = parse_theorem(
        &fmt,
        "wff x0, wff x1, wff x2 => |- ((x0 -> (x1 -> x2)) -> ((x0 -> x1) -> (x0 -> x2)))",
    );
    let ax_mp = parse_theorem(&fmt, "|- x0, |- (x0 -> x1) => |- x1");
    DBTheorem::insert_without_id(&conn, &wff2, false);
    DBTheorem::insert_without_id(&conn, &ax1, true);
    DBTheorem::insert_without_id(&conn, &ax2, true);
    DBTheorem::insert_without_id(&conn, &ax_mp, true);

    for _ in 0..50 {
        let ts = find_good_theorem(&conn, 1);
        for t in ts.iter() {
            println!("{}", t.to_theorem().format(&fmt));
            proof_all(&conn, t);
        }

        println!("ok");
    }

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
