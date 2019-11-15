use crate::{
    statement::Statement,
    theorem::{DBTheorem, Theorem},
};
use diesel::prelude::*;
use diesel::sqlite::SqliteConnection;

sql_function! {
    fn length(x: diesel::sql_types::Binary) -> diesel::sql_types::Integer;
}

pub fn max_id(conn: &SqliteConnection) -> i32 {
    use crate::schema::theorem::dsl::*;
    theorem
        .select(id)
        .order(id.desc())
        .limit(1)
        .load(conn)
        .unwrap()[0]
}

pub fn score_new_min(conn: &SqliteConnection) -> i32 {
    use crate::schema::theorem_new::dsl::*;
    theorem_new
        .select(n_score)
        .order(n_score.asc())
        .limit(1)
        .load(conn)
        .unwrap()[0]
}

pub fn introduce_new(conn: &SqliteConnection, max_score: i32) {
    use crate::schema::theorem::dsl::*;
    use crate::schema::theorem_new::dsl::*;
    let new_theorems = theorem_new.filter(n_score.le(max_score));
    diesel::insert_or_ignore_into(theorem)
        .values(new_theorems.select((n_conclusion, n_assumptions, n_dvrs, n_score)))
        .into_columns((conclusion, assumptions, dvrs, score))
        .execute(conn)
        .unwrap();
    diesel::delete(new_theorems).execute(conn).unwrap();
}

pub fn find_good_theorem(conn: &SqliteConnection, limit: usize) -> Vec<DBTheorem> {
    use crate::schema::theorem::dsl::*;
    let max_id = max_id(conn);
    theorem
        .filter(use_for_proof.eq(1))
        .filter((last_auto * score).lt(max_id))
        .order(score.asc())
        .limit(limit as i64)
        .load(conn)
        .unwrap()
}

pub fn find_matching_candidates(
    conn: &SqliteConnection,
    search: &Statement,
    min_id: i32,
    max_id: i32,
) -> Vec<DBTheorem> {
    use crate::schema::theorem::dsl::*;
    let (low, high) = search.match_bounds();
    theorem
        .filter(conclusion.ge(low.serialize()))
        .filter(conclusion.lt(high.serialize()))
        .filter(id.gt(min_id))
        .filter(id.le(max_id))
        .load(conn)
        .unwrap()
}

pub fn proof_all(conn: &SqliteConnection, db_th: &DBTheorem) -> Vec<Theorem> {
    let th = db_th.to_theorem();
    let mut inserts = Vec::new();
    let max_id = max_id(conn);
    let min_id = db_th.last_auto();

    if min_id == 0 {
        proof_all_simplify(&th, &mut inserts);
    }
    proof_all_combine(conn, &th, min_id, max_id, &mut inserts);

    use crate::schema::theorem::dsl::*;
    diesel::update(theorem.filter(id.eq(db_th.id())))
        .set(last_auto.eq(max_id))
        .execute(conn)
        .unwrap();
    inserts
}

pub fn proof_all_simplify(th: &Theorem, inserts: &mut Vec<Theorem>) {
    for i in 0..th.assumptions().len() {
        for j in 0..i {
            if let Ok(res) = th.simplify(i as i16, j as i16) {
                inserts.push(res);
            }
        }
    }
}

pub fn proof_all_combine(
    conn: &SqliteConnection,
    th: &Theorem,
    min_id: i32,
    max_id: i32,
    inserts: &mut Vec<Theorem>,
) {
    for (i, asmpt) in th.assumptions().iter().enumerate() {
        let candidates = find_matching_candidates(conn, asmpt, min_id, max_id);
        for other_db in candidates {
            let other = other_db.to_theorem();
            if let Ok(res) = th.combine(&other, i) {
                inserts.push(res);
            }
        }
    }
}
