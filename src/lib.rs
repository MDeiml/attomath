#![feature(slice_group_by)]
//! `attomath` is a system for formalizing and proving mathematical theorems heavily inspired by
//! [Metamath](http://us.metamath.org/mm.html). `attomath` aims to be as small as possible while
//! still being able to describe any axiomatic system.
//!
//! # Main data structures
//! There are four main data structures in `attomath`: [`Expression`]s,
//! [`Statement`], [`DVR`] and [`Theorem`].
//!
//! ## Expressions
//! A [`Expression`] is a binary AST (abstract syntax tree) and typically represents
//! something like _a -> a_ or _a = b_. This is different from Metamath where expressions are
//! encoded as strings. Using a AST instead makes comparisons and substitutions for expressions
//! faster and more consistent, as it more closely represents the underlying formula.
//!
//! ## Statements
//! A [`Statement`] in `attomath` could represent something like _a -> a is provable_
//! or _a = b is syntactically correct_.  It consists of a judgement (_is provable_, _is
//! syntactically correct_) and a [`Expression`] (_a -> a_, _a = b_).
//!
//! ## DVRs
//! A [`DVR`] is a way of preventing two variables to be equal.
//!
//! In general it is assumed, that a [`Statement`] does not change its meaning if a
//! variable is replaced with another variable, but this is not true in all cases. For this purpose
//! one can specify that two variables should not be replaced with the same variable or expressions
//! containing a common variable.
//!
//! ## Theorems
//! A [`Theorem`] consists of zero or more assumptions ([`Statement`]s) and
//! [`DVR`]s and one conclusion (also a [`Statement`]). This makes it possible to
//! formulate something like _if a is provable and a -> b is provable then b is provable_. In this
//! case _a is provable_ and _a -> b is provable_ are assumptions and _b is provable_ is a
//! conclusion.
//!
//! The structs interface guarantees that only valid theorems can be produced if only axioms are
//! constructed using [`Theorem::new`], while still being able to crate any theorem that can be
//! proven from the given axioms.
//!
//! In `attomath`, unlike Metamath, all assumptions (called Hypothesis in Metamath) for a theorem
//! are stored together with their corresponding theorem. This way variables carry no meaning
//! outside a theorem, and the context for a statement is always the theorem of that statement.
//! This means that `attomath`s format is less compact, since "variable types" like _formula_ or
//! _set variable_ have to be declared for every theorem. But it also leads to a more consistent
//! format where a theorem is self-contained.

#[cfg(feature = "serialization")]
extern crate nom;
#[cfg(test)]
#[macro_use]
extern crate quickcheck;

mod dvr;
pub mod error;
pub mod expression;
pub mod serialization;
mod statement;
mod theorem;
mod types;

pub use dvr::*;
pub use expression::Expression;
pub use statement::*;
pub use theorem::*;
pub use types::*;
