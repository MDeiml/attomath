# attomath

`attomath` is a system for formalizing and proving mathematical theorems heavily inspired by
[Metamath](http://us.metamath.org/mm.html). `attomath` aims to be as small as possible while
still being able to describe any axiomatic system.

## Main data structures
There are three main data structures in `attomath`: [`Statement`s][statement], [`DVR`s][dvr]
and [`Theorem`s][theorem].

### Statements
A [`Statement`][statement] in `attomath` could represent something like _a -> a is provable_
or _a = b is syntactically correct_.  It consists of a judgement (_is provable_, _is
syntactically correct_) and a expression (_a -> a_, _a = b_). What differentiates `attomath`
most from Metamath is that expressions are not stored as a string, but as a (binary) syntax
tree encoded as a sequence in prefix order. This makes comparisons and substitutions faster and
more consistent.

### DVRs
A [`DVR`][dvr] is a way of preventing two variables to be equal.

In general it is assumed, that a [`Statement`][statement] does not change its meaning if a
variable is replaced with another variable, but this is not true in all cases. For this one can
specify that two variables should not be replaced with the same variable or expressions
containing a common variable.

### Theorems
A [`Theorem`][theorem] consists of zero or more assumptions ([`Statement`s][statement]) and
[`DVR`s][dvr] and one conclusion (also a [`Statement`][statement]). This makes it possible to
formulate something like _if a is provable and a -> b is provable then b is provable_. In this
case _a is provable_ and _a -> b is provable_ are assumptions and _b is provable_ is a
conclusion.

The structs interface guarantees that only valid theorems can be produced if only axioms are
constructed using [`Theorem::new`](theorem/struct.Theorem.html#method.new), while still being
able to crate any theorem that can be proven from the given axioms (these claims are not yet
proven).

In `attomath`, unlike Metamath, all assumptions (called Hypothesis in Metamath) for a theorem
are stored together with their corresponding theorem. This way variables carry no meaning
outside a theorem, and the context for a statement is always the theorem of that statement.
This means that `attomath`s format is less compact, since "variable types" like _formula_ or
_set variable_ have to be declared for every theorem. But it also leads to a more consistent
format where a theorem is self-contained.

[statement]: statement/trait.Statement.html
[dvr]: dvr/struct.DVR.html
[theorem]: theorem/struct.Theorem.html

