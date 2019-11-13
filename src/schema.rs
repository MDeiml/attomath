table! {
    theorem (id) {
        id -> Integer,
        conclusion -> Binary,
        assumptions -> Binary,
        dvrs -> Binary,
        description -> Nullable<Text>,
    }
}
