use crate::{error::ProofError, types::*};
use std::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    ops::RangeBounds,
};

#[derive(Clone, Eq, Ord, Debug, Copy)]
pub struct Expression<T: Borrow<[Identifier]>> {
    data: T,
}

impl<T: Borrow<[Identifier]>, S: Borrow<[Identifier]>> PartialEq<Expression<S>> for Expression<T> {
    fn eq(&self, other: &Expression<S>) -> bool {
        self.data.borrow() == other.data.borrow()
    }
}

impl<T: Borrow<[Identifier]>, S: Borrow<[Identifier]>> PartialOrd<Expression<S>> for Expression<T> {
    fn partial_cmp(&self, other: &Expression<S>) -> Option<Ordering> {
        // code is safe, because i16 and u16 have the same memory layout
        unsafe {
            let a: &[i16] = self.data.borrow();
            let a_transmuted: &[u16] = std::mem::transmute(a);
            let b: &[i16] = other.data.borrow();
            let b_transmuted: &[u16] = std::mem::transmute(b);
            a_transmuted.partial_cmp(b_transmuted)
        }
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
    pub fn standardize(&mut self, var_map: &mut [Option<Identifier>], next_var: &mut Identifier) {
        self.standardize_range(var_map, next_var, ..);
    }

    pub(crate) fn standardize_range<R: RangeBounds<Identifier>>(
        &mut self,
        var_map: &mut [Option<Identifier>],
        next_var: &mut Identifier,
        range: R,
    ) {
        for symb in self.data.borrow_mut().iter_mut() {
            if !is_operator(*symb) && range.contains(symb) {
                let var = var_map[*symb as usize].unwrap_or_else(|| {
                    let var = *next_var;
                    var_map[*symb as usize] = Some(var);
                    *next_var += 1;
                    var
                });
                if range.contains(&var) {
                    *symb = var;
                }
            }
        }
    }

    pub(crate) fn substitute_variables(&mut self, var_map: &[Option<Identifier>]) {
        for symb in self.data.borrow_mut().iter_mut() {
            if !is_operator(*symb) {
                if let Some(sub) = var_map[*symb as usize] {
                    *symb = sub;
                }
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
                "Somehow an invalid expression was formed: {:?}",
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
            if is_operator(s) && s != Identifier::MIN {
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
/// use attomath::{expression::is_operator, Identifier};
///
/// assert!(is_operator(-2));
/// assert!(is_operator(Identifier::MIN));
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
    type T = [Identifier; 1];

    fn substitution_opt(&self, id: Identifier) -> Option<Expression<[Identifier; 1]>> {
        if id < 0 {
            panic!("id is not a variable");
        }
        Some(Expression {
            data: [id + self.shift as Identifier],
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

/// A single variable [`Substitution`](trait.Substitution.html)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleSubstitution(Identifier, Identifier);

impl SingleSubstitution {
    /// Creates a substitution with the capacity to store replacements for variables `0` to
    /// `n - 1`.
    pub fn new(a: Identifier, b: Identifier) -> Self {
        SingleSubstitution(a, b)
    }
}

impl Substitution for SingleSubstitution {
    type T = [Identifier; 1];

    fn substitution_opt(&self, id: Identifier) -> Option<Expression<[Identifier; 1]>> {
        if id == self.0 {
            Some(Expression { data: [self.1] })
        } else {
            None
        }
    }
}

/// A complete variable [`Substitution`](trait.Substitution.html)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariableSubstitution<T: Borrow<[Option<Identifier>]>>(T);

impl<T: Borrow<[Option<Identifier>]>> VariableSubstitution<T> {
    /// Creates a substitution with the capacity to store replacements for variables `0` to
    /// `n - 1`.
    pub fn new(variables: T) -> Self {
        VariableSubstitution(variables)
    }
}

impl<S: Borrow<[Option<Identifier>]>> Substitution for VariableSubstitution<S> {
    type T = [Identifier; 1];

    fn substitution_opt(&self, id: Identifier) -> Option<Expression<[Identifier; 1]>> {
        // TODO: Check variable is variable
        self.0.borrow()[id as usize].map(|v| Expression { data: [v] })
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

#[cfg(test)]
mod tests {
    use std::num::Wrapping;

    use quickcheck::Arbitrary;

    use super::*;

    impl Arbitrary for Expression<Box<[Identifier]>> {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            loop {
                let data = Vec::<Identifier>::arbitrary(g).into_boxed_slice();
                if let Some(subexpression) = Expression::subexpression_check(&data, 0) {
                    return Expression {
                        data: subexpression.data.to_owned().into_boxed_slice(),
                    };
                }
            }
        }
    }

    quickcheck! {
        fn unify_substitute(a: Expression<Box<[Identifier]>>, b: Expression<Box<[Identifier]>>) -> bool {
            let max_var = b.variables().max().unwrap_or(-1);
            let mut substitution =
                WholeSubstitution::with_capacity((Wrapping(max_var as usize) + Wrapping(1)).0);
            match a.unify(&b, &mut substitution) {
                Ok(()) => b.substitute(&substitution) == a,
                Err(_) => true
            }
        }
    }
}
