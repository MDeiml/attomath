-- This file should undo anything in `up.sql`
DROP INDEX conclusion;
DROP INDEX theorem_uniq;
DROP INDEX theorem_new_uniq;
DROP INDEX theorem_score;
DROP INDEX theorem_score_new;
DROP TABLE theorem;
DROP TABLE theorem_new;
