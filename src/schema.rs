table! {
    theorem (id) {
        id -> Integer,
        conclusion -> Binary,
        assumptions -> Binary,
        dvrs -> Binary,
        description -> Nullable<Text>,
        last_auto -> Integer,
        use_for_proof -> Integer,
    }
}
