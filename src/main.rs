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
use statement::Statement;
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
    let wff3 = parse_theorem(&fmt, "wff x0 => wff (-. x0)");
    let ax1 = parse_theorem(&fmt, "wff x0, wff x1 => |- (x0 -> (x1 -> x0))");
    let ax2 = parse_theorem(
        &fmt,
        "wff x0, wff x1, wff x2 => |- ((x0 -> (x1 -> x2)) -> ((x0 -> x1) -> (x0 -> x2)))",
    );
    let ax3 = parse_theorem(
        &fmt,
        "wff x0, wff x1 => |- (((-. x0) -> (-. x1)) -> (x1 -> x0))",
    );
    let ax_mp = parse_theorem(&fmt, "|- x0, |- (x0 -> x1) => |- x1");
    let id = parse_theorem(&fmt, "wff x0 => |- (x0 -> x0)");
    let id_con = id.conclusion().serialize();
    let id_asmpt = Statement::serialize_vec(id.assumptions());
    DBTheorem::insert_without_id(&conn, &wff2, false);
    DBTheorem::insert_without_id(&conn, &wff3, false);
    DBTheorem::insert_without_id(&conn, &ax1, true);
    DBTheorem::insert_without_id(&conn, &ax2, true);
    DBTheorem::insert_without_id(&conn, &ax3, true);
    DBTheorem::insert_without_id(&conn, &ax_mp, true);

    loop {
        let ts = find_good_theorem(&conn, 5);
        if ts.is_empty() {
            intorduce_new(&conn);
            use schema::theorem::dsl::*;
            let test: Vec<DBTheorem> = theorem
                .filter(conclusion.eq(&id_con))
                .filter(assumptions.eq(&id_asmpt))
                .limit(1)
                .load(&conn)
                .unwrap();
            if !test.is_empty() {
                println!("{}", test[0].to_theorem().format(&fmt));
                return;
            }
        } else {
            for t in ts.iter() {
                proof_all(&conn, t);
            }
        }
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
