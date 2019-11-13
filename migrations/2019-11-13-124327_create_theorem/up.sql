-- Your SQL goes here
CREATE TABLE theorem (
    id INTEGER PRIMARY KEY NOT NULL,
    conclusion BLOB NOT NULL,
    assumptions BLOB NOT NULL,
    dvrs BLOB NOT NULL,
    description TEXT NULL
);
