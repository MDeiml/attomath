-- Your SQL goes here
CREATE TABLE theorem (
    id INTEGER PRIMARY KEY NOT NULL,
    conclusion BLOB NOT NULL,
    assumptions BLOB NOT NULL,
    dvrs BLOB NOT NULL,
    last_auto INTEGER NOT NULL DEFAULT 0,
    use_for_proof INTEGER NOT NULL DEFAULT 1,
    score INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE theorem_new (
    id INTEGER PRIMARY KEY NOT NULL,
    n_conclusion BLOB NOT NULL,
    n_assumptions BLOB NOT NULL,
    n_dvrs BLOB NOT NULL,
    n_score INTEGER NOT NULL DEFAULT 0
);
CREATE INDEX conclusion ON theorem (conclusion);
CREATE INDEX theorem_score ON theorem (score);
CREATE INDEX theorem_score_new ON theorem_new (n_score);
CREATE UNIQUE INDEX theorem_uniq ON theorem(conclusion, assumptions, dvrs);
CREATE UNIQUE INDEX theorem_new_uniq ON theorem_new(n_conclusion, n_assumptions, n_dvrs);
