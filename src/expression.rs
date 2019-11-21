use crate::{error::ProofError, types::*};
use std::borrow::{Borrow, BorrowMut};

#[derive(Clone, Eq, PartialOrd, Ord, Debug, Copy)]
pub struct Expression<T: Borrow<[Identifier]>> {
    data: T,
}

impl<T: Borrow<[Identifier]>, S: Borrow<[Identifier]>> PartialEq<Expression<S>> for Expression<T> {
    fn eq(&self, other: &Expression<S>) -> bool {
        self.data.borrow() == other.data.borrow()
    }
}

impl<T: BorrowMut<[Identifier]>> Expression<T> {
    /// Turns this expression into its standard representation, numbering variables in the order of
    /// their apperance.
    ///
    /// # Example
    /// ```
    /// use attomath::expression::Expression;
    ///
    /// let mut s = Expression::from_raw(vec![-2, -2, 2, 0, 2]).unwrap();
    /// let mut var_map = vec![None; 6];
    /// var_map[2] = Some(3);
    /// let mut next_var = 5;
    /// s.standardize(&mut var_map, &mut next_var);
    /// assert_eq!(s.data(), &[-2, -2, 3, 5, 3]);
    /// assert_eq!(var_map, vec![Some(5), None, Some(3), None, None, None]);
    /// assert_eq!(next_var, 6);
    /// ```
    pub fn standardize(
        &mut self,
        var_map: &mut Vec<Option<Identifier>>,
        next_var: &mut Identifier,
    ) {
        for symb in self.data.borrow_mut().iter_mut() {
            if !is_operator(*symb) {
                *symb = var_map[*symb as usize].unwrap_or_else(|| {
                    let var = *next_var;
                    var_map[*symb as usize] = Some(var);
                    *next_var += 1;
                    var
                });
            }
        }
    }
}

impl<T: Borrow<[Identifier]> + std::fmt::Debug> Expression<T> {
    pub fn data<'a>(&'a self) -> &'a T {
        &self.data
    }

    pub fn to_slice<'a>(&'a self) -> Expression<&'a [Identifier]> {
        Expression {
            data: self.data.borrow(),
        }
    }

    pub fn from_raw(expr: T) -> Option<Self> {
        if Self::check(&expr) {
            Some(Expression { data: expr })
        } else {
            None
        }
    }

    pub fn variables<'a>(&'a self) -> impl Iterator<Item = Identifier> + 'a {
        self.data
            .borrow()
            .iter()
            .copied()
            .filter(|s| !is_operator(*s))
    }

    /// Returns the subexpression beginning at the given index.
    ///
    /// # Panics
    /// This method panics if start_index is not in the range `0..self.data().borrow().len()`
    ///
    /// # Example
    /// ```
    /// use attomath::expression::Expression;
    ///
    /// let st = Expression::from_raw(vec![-2, 0, -2, 1, 0]).unwrap();
    /// assert_eq!(*st.subexpression(2).data(), &[-2, 1, 0]);
    /// assert_eq!(*st.subexpression(3).data(), &[1]);
    /// ```
    pub fn subexpression<'a>(&'a self, start_index: usize) -> Expression<&'a [Identifier]> {
        Self::subexpression_check(&self.data, start_index).expect(
            format!(
                "Somehow a invalid expression was formed: {:?}",
                self.borrow()
            )
            .as_str(),
        )
    }

    /// Calculates a `Substitution` which transforms `other` into `this`. If this function suceeds
    /// then it is guaranteed that `other.substitute(&substitution) == self`.
    ///
    /// # Errors
    /// * OperatorMismatch - if the operators of `other` do not match the corresponding operators
    /// of `self`
    /// * VariableMismatch - if a variable in `other` would have to be substituted by two different
    /// expressions
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{Expression, WholeSubstitution};
    /// use attomath::error::ProofError;
    ///
    /// let a = Expression::from_raw(vec![-2, 0, -2, 1, 0]).unwrap();
    /// let b = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub); // (x0 ~> x0, x1 ~> (x1 -> x0))
    /// assert_eq!(result, Ok(()));
    /// assert_eq!(b.substitute(&sub), a);
    ///
    /// let a = Expression::from_raw(vec![-2, 0, -2, 1, 0]).unwrap();
    /// let b = Expression::from_raw(vec![-2, 0, 0]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub); // (x0 ~> x0, x0 ~> (x1 -> x0))
    /// assert_eq!(result, Err(ProofError::VariableMismatch(
    ///     0,
    ///     vec![0].into_boxed_slice(),
    ///     vec![-2, 1, 0].into_boxed_slice(),
    /// )));
    ///
    /// let a = Expression::from_raw(vec![-3, 0, -2, 1, 0]).unwrap();
    /// let b = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub);
    /// assert_eq!(result, Err(ProofError::OperatorMismatch(-3, -2)));
    /// ```
    pub fn unify<'a, S: Borrow<[Identifier]>>(
        &'a self,
        other: &Expression<S>,
        substitution: &mut WholeSubstitution<'a>,
    ) -> Result<(), ProofError> {
        let expr = self.data.borrow();
        let mut expr_index = 0;
        for &symb in other.data.borrow().iter() {
            if is_operator(symb) {
                let symb_self = expr[expr_index];
                expr_index += 1;
                if symb_self != symb {
                    return Err(ProofError::OperatorMismatch(symb_self, symb));
                }
            } else {
                if let Some(old) = substitution.substitution_opt(symb) {
                    let start = expr_index;
                    expr_index += old.data.len();
                    if self.data.borrow().len() < expr_index
                        || old.data != &self.data.borrow()[start..expr_index]
                    {
                        return Err(ProofError::VariableMismatch(
                            symb,
                            Box::from(old.data),
                            Box::from(self.subexpression(start).data.borrow()),
                        ));
                    }
                } else {
                    let subexpr = self.subexpression(expr_index);
                    expr_index += subexpr.data.borrow().len();
                    substitution.insert(
                        symb,
                        Expression {
                            data: subexpr.data.borrow(),
                        },
                    );
                }
            }
        }
        return Ok(());
    }

    /// Use the given substitution on this expression to create a new expression
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{Expression, WholeSubstitution};
    ///
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let expr = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// sub.insert(0, expr.to_slice());
    /// assert_eq!(*expr.substitute(&sub).to_slice().data(), &[-2, -2, 0, 1, 1]);
    /// ```
    pub fn substitute<S: Substitution>(&self, substitution: &S) -> Expression<Box<[Identifier]>> {
        let mut new_expr = Vec::with_capacity(self.data.borrow().len());
        for symb in self.data.borrow().iter() {
            if is_operator(*symb) {
                new_expr.push(*symb)
            } else {
                if let Some(e) = substitution.substitution_opt(*symb) {
                    new_expr.extend_from_slice(e.data.borrow());
                } else {
                    new_expr.push(*symb);
                }
            }
        }
        Expression {
            data: new_expr.into_boxed_slice(),
        }
    }

    fn check(expr: &T) -> bool {
        Self::subexpression_check(expr, 0).map(|s| s.data.borrow().len())
            == Some(expr.borrow().len())
    }

    fn subexpression_check<'a>(
        expr: &'a T,
        start_index: usize,
    ) -> Option<Expression<&'a [Identifier]>> {
        let mut depth = 1;
        for (i, &s) in expr.borrow()[start_index..].iter().enumerate() {
            if is_operator(s) && s != -1 {
                depth += 1;
            } else {
                depth -= 1;
            }
            if depth == 0 {
                return Some(Expression {
                    data: &expr.borrow()[start_index..=start_index + i],
                });
            }
        }
        None
    }
}

/// Tests whether the given identifier is an operator
///
/// # Example
/// ```
/// use attomath::expression::is_operator;
///
/// assert!(is_operator(-2));
/// assert!(is_operator(-1));
/// assert!(!is_operator(0));
/// ```
pub fn is_operator(x: Identifier) -> bool {
    x < 0
}

pub struct ChainSubstitution<S: Substitution, T: Substitution> {
    pub first: S,
    pub then: T,
}

#[derive(Debug)]
pub enum Either<S, T> {
    Left(S),
    Right(T),
}

impl<S: Borrow<[Identifier]>, T: Borrow<[Identifier]>> Borrow<[Identifier]> for Either<S, T> {
    fn borrow(&self) -> &[Identifier] {
        use Either::*;
        match self {
            Left(expr) => expr.borrow(),
            Right(expr) => expr.borrow(),
        }
    }
}

impl<S: Substitution, T: Substitution> Substitution for ChainSubstitution<S, T> {
    type T = Either<S::T, T::T>;

    fn substitution_opt(&self, id: Identifier) -> Option<Expression<Self::T>> {
        self.first
            .substitution_opt(id)
            .map(|s| Expression {
                data: Either::Left(s.data),
            })
            .or_else(|| {
                self.then.substitution_opt(id).map(|s| Expression {
                    data: Either::Right(s.data),
                })
            })
    }
}

pub struct ShiftSubstitution {
    shift: Identifier,
}

impl ShiftSubstitution {
    pub fn new(shift: Identifier) -> Self {
        if shift < 0 {
            panic!("shift must be greater than zero");
        }
        ShiftSubstitution { shift }
    }
}

impl Substitution for ShiftSubstitution {
    type T = Box<[Identifier]>;

    fn substitution_opt(&self, id: Identifier) -> Option<Expression<Box<[Identifier]>>> {
        if id < 0 {
            panic!("id is not a variable");
        }
        Some(Expression {
            data: vec![id + self.shift as Identifier].into_boxed_slice(),
        })
    }
}

/// A general [`Substitution`](trait.Substitution.html)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WholeSubstitution<'a> {
    substitution: Vec<Option<Expression<&'a [Identifier]>>>,
}

impl<'a> WholeSubstitution<'a> {
    /// Creates a substitution with the capacity to store replacements for variables `0` to
    /// `n - 1`.
    pub fn with_capacity(n: usize) -> Self {
        WholeSubstitution {
            substitution: vec![None; n],
        }
    }

    /// Marks the `id` to be substituted by `expr`.
    ///
    /// # Panics
    /// This method panics if `id` is not in the range of this substitutions capacity
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{Expression, Substitution, WholeSubstitution};
    ///
    /// let expr = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.to_slice());
    /// assert_eq!(sub.substitution_opt(0), Some(expr.to_slice()));
    /// assert_eq!(sub.substitution_opt(1), None);
    /// ```
    pub fn insert(&mut self, id: Identifier, expr: Expression<&'a [Identifier]>) {
        self.substitution[id as usize] = Some(expr)
    }
}

impl<'a> Substitution for WholeSubstitution<'a> {
    type T = &'a [Identifier];

    fn substitution_opt(&self, id: Identifier) -> Option<Expression<&'a [Identifier]>> {
        self.substitution[id as usize]
    }
}

/// A `Substitution` maps variable ids to expressions (represented by a sequence of identifiers).
///
/// This is intented to be used together with [`Expression`s](struct.Expression.html).
pub trait Substitution {
    type T: Borrow<[Identifier]> + std::fmt::Debug;

    /// Get the stored substitution for the variable with identifier `id`. Or `None` if the
    /// variable should not be replaced.
    ///
    /// # Panics
    /// This may panic if `id` is not in the range of the particular substitution.
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{Substitution, WholeSubstitution, Expression};
    ///
    /// let expr = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.to_slice());
    /// assert_eq!(sub.substitution_opt(0), Some(expr.to_slice()));
    /// assert_eq!(sub.substitution_opt(1), None);
    /// ```
    fn substitution_opt(&self, id: Identifier) -> Option<Expression<Self::T>>;
}
