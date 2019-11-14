table! {
    theorem (id) {
        id -> Integer,
        conclusion -> Binary,
        assumptions -> Binary,
        dvrs -> Binary,
        last_auto -> Integer,
        use_for_proof -> Integer,
        score -> Integer,
    }
}

table! {
    theorem_new (id) {
        id -> Integer,
        n_conclusion -> Binary,
        n_assumptions -> Binary,
        n_dvrs -> Binary,
        n_score -> Integer,
    }
}

allow_tables_to_appear_in_same_query!(
    theorem,
    theorem_new,
);
