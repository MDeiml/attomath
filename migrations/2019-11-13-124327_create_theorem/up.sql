-- Your SQL goes here
CREATE TABLE theorem (
    id INTEGER PRIMARY KEY NOT NULL,
    conclusion BLOB NOT NULL,
    assumptions BLOB NOT NULL,
    dvrs BLOB NOT NULL,
    description TEXT,
    last_auto INTEGER NOT NULL DEFAULT 0,
    use_for_proof INTEGER NOT NULL DEFAULT 1
);
CREATE INDEX conclusion ON theorem (conclusion);
CREATE UNIQUE INDEX theorem_uniq ON theorem(conclusion, assumptions, dvrs);
