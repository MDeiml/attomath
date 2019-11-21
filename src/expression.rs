use crate::{error::ProofError, types::*};
#[cfg(feature = "use-serde")]
use serde::{de::Error, Deserialize, Deserializer, Serialize};
use std::borrow::{Borrow, BorrowMut};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Copy)]
#[cfg_attr(feature = "use-serde", derive(Serialize))]
pub struct Expression<T: Borrow<[Identifier]>> {
    data: T,
}

#[cfg(feature = "use-serde")]
impl<'de, T: Borrow<[Identifier]> + std::fmt::Debug + From<Vec<Identifier>> + Deserialize<'de>>
    Deserialize<'de> for Expression<T>
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let data: Vec<_> = Deserialize::deserialize(deserializer)?;
        Expression::from_raw(From::from(data)).ok_or(D::Error::custom("data not well formated"))
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
    /// assert_eq!(*st.subexpression(2).data(), vec![-2, 1, 0].as_slice());
    /// assert_eq!(*st.subexpression(3).data(), vec![1].as_slice());
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

    fn check(expr: &T) -> bool {
        Self::subexpression_check(expr, 0).map(|s| s.data.borrow().len())
            == Some(expr.borrow().len())
    }

    /// Calculates a `Substitution` which transforms `other` into `this`.
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
    /// let a = Expression::from_raw(vec![-2, 0, -2, 1, 0].into_boxed_slice()).unwrap();
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
        let mut expr_iter = self.data.borrow().iter();
        let mut expr_index = 0;
        for &symb in other.data.borrow().iter() {
            if is_operator(symb) {
                let symb_self = *expr_iter
                    .next()
                    .expect(format!("self is not well formated {:?}", self.borrow()).as_str());
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
                    for _ in 0..old.data.len() {
                        expr_iter.next();
                    }
                } else {
                    let subexpr = self.subexpression(expr_index);
                    expr_index += subexpr.data.borrow().len();
                    for _ in 0..subexpr.data.borrow().len() {
                        expr_iter.next();
                    }
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
    /// assert_eq!(*expr.substitute(&sub).data(), vec![-2, -2, 0, 1, 1].into_boxed_slice());
    /// ```
    pub fn substitute<'a, S: Substitution<'a>>(
        &self,
        substitution: &'a S,
    ) -> Expression<Box<[Identifier]>> {
        let mut new_expr = Vec::with_capacity(self.data.borrow().len());
        for &symb in self.data.borrow().iter() {
            if is_operator(symb) {
                new_expr.push(symb)
            } else {
                new_expr.extend_from_slice(substitution.substitution(&symb).data);
            }
        }
        Expression {
            data: new_expr.into_boxed_slice(),
        }
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

    /// Replaces any unsubstituted variable with the identifier in `other` (indexed by the current
    /// variable id).
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{Expression, Substitution, WholeSubstitution};
    ///
    /// let expr = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.to_slice());
    /// let rem = vec![
    ///     Expression::from_raw(vec![2]).unwrap(),
    ///     Expression::from_raw(vec![3]).unwrap()
    /// ];
    /// sub.substitute_remaining(rem.as_slice());
    /// assert_eq!(sub.substitution_opt(0), Some(expr.to_slice()));
    /// assert_eq!(sub.substitution_opt(1), Some(rem[1].to_slice()));
    /// ```
    pub fn substitute_remaining<T: Borrow<[Identifier]> + std::fmt::Debug>(
        &mut self,
        other: &'a [Expression<T>],
    ) {
        for (expr, sub) in other.iter().zip(self.substitution.iter_mut()) {
            if sub.is_none() {
                *sub = Some(expr.to_slice());
            }
        }
    }

    /// Marks the `id` to be substituted by `expr`. This does not check whether `expr` is a valid
    /// expression.
    ///
    /// # Panics
    /// This method panics if `id` is not in the range `0..=self.max_var()`.
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

impl<'a> Substitution<'a> for WholeSubstitution<'a> {
    fn substitution_opt(&self, id: Identifier) -> Option<Expression<&'a [Identifier]>> {
        self.substitution[id as usize]
    }

    fn max_var(&self) -> Identifier {
        self.substitution.len() as i16 - 1
    }
}

/// A 1:1 [`Substitution`](trait.Substitution.html) for a single variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleSubstitution<'a> {
    from: Identifier,
    to: Expression<&'a [Identifier]>,
}

impl<'a> SingleSubstitution<'a> {
    /// Creates a new `SingleSubstitution` substituting `from` with `to`.
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{Substitution, SingleSubstitution, Expression};
    ///
    /// let expr = Expression::from_raw(vec![-2, 3, 1]).unwrap();
    /// let sub = SingleSubstitution::new(2, expr.to_slice());
    /// assert_eq!(sub.substitution_opt(0), None);
    /// assert_eq!(sub.substitution_opt(2), Some(expr.to_slice()));
    /// ```
    pub fn new(from: Identifier, to: Expression<&'a [Identifier]>) -> Self {
        SingleSubstitution { from, to }
    }
}

impl<'a> Substitution<'a> for SingleSubstitution<'a> {
    fn substitution_opt(&self, id: Identifier) -> Option<Expression<&'a [Identifier]>> {
        if id == self.from {
            Some(self.to)
        } else {
            None
        }
    }

    fn max_var(&self) -> Identifier {
        self.from
    }
}

/// A `Substitution` maps variable ids to expressions (represented by a sequence of identifiers).
///
/// This is intented to be used together with [`Expression`s](struct.Expression.html).
pub trait Substitution<'a> {
    /// Get the stored substitution for the variable with identifier `id`. Or `None` if the
    /// variable should not be replaced.
    ///
    /// # Panics
    /// This may panic if `id` is not in the range `0..=self.max_var()`.
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
    fn substitution_opt(&self, id: Identifier) -> Option<Expression<&'a [Identifier]>>;

    /// Get the maximum variable id that can be stored in this substitution.
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{
    ///     WholeSubstitution, SingleSubstitution, Substitution, Expression
    /// };
    ///
    /// let sub = WholeSubstitution::with_capacity(20);
    /// assert_eq!(sub.max_var(), 19);
    ///
    /// let expr = Expression::from_raw(vec![10]).unwrap();
    /// let sub = SingleSubstitution::new(4, expr.to_slice());
    /// assert_eq!(sub.max_var(), 4);
    /// ```
    fn max_var(&self) -> Identifier;

    /// Get the stored substitution for the variable with identifier `id`. Returns `[id]` if the
    /// variable should not be replaced.
    ///
    /// # Panics
    /// This may panic if `id` is not in the range `0..=self.max_var()`.
    ///
    /// # Example
    /// ```
    /// use attomath::expression::{WholeSubstitution, Substitution, Expression};
    ///
    /// let expr = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.to_slice());
    /// assert_eq!(sub.substitution(&0), expr.to_slice());
    /// assert_eq!(sub.substitution(&1), Expression::from_raw(vec![1]).unwrap().to_slice());
    /// ```
    fn substitution<'b>(&'a self, id: &'b Identifier) -> Expression<&'b [Identifier]>
    where
        'a: 'b,
    {
        self.substitution_opt(*id).unwrap_or(Expression {
            data: std::slice::from_ref(id),
        })
    }
}
