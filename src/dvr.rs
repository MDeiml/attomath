use crate::{
    error::ProofError,
    expression::{is_operator, Substitution},
    types::*,
};
#[cfg(feature = "use-serde")]
use serde::{Deserialize, Serialize};

pub struct Iter {
    a: Vec<Identifier>,
    b: Vec<Identifier>,
    index: usize,
}

impl Iterator for Iter {
    type Item = Result<DVR, ProofError>;

    fn next(&mut self) -> Option<Result<DVR, ProofError>> {
        if self.index >= self.a.len() * self.b.len() {
            return None;
        }
        let res = DVR::new(
            self.a[self.index % self.a.len()],
            self.b[self.index / self.a.len()],
        );
        self.index += 1;
        Some(res)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.a.len() * self.b.len() - self.index;
        (rem, Some(rem))
    }
}

/// A _distince variable relation_ for expressing that two variables must be different.
///
/// In the default case it is always assumed that all statements are correct if you replace
/// a variable with a different subexpression. This leads to logical errors in statements like
/// `forall x0. exists x1. x0 != x1`.
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
#[cfg_attr(feature = "use-serde", derive(Serialize, Deserialize))]
pub struct DVR(Identifier, Identifier);

impl DVR {
    /// Returns this `DVR`s variables
    pub fn variables(&self) -> (Identifier, Identifier) {
        let DVR(a, b) = self;
        (*a, *b)
    }

    /// Creates a new `DVR` restricting `a` and `b` from being the same variable.
    ///
    /// # Errors
    /// This function fails with a `DVRError` if `a == b`
    ///
    /// # Example
    /// ```
    /// use attomath::dvr::DVR;
    /// use attomath::error::ProofError;
    ///
    /// let dvr = DVR::new(0, 1);
    /// assert_eq!(dvr.map(|d| d.variables()), Ok((0, 1)));
    ///
    /// let dvr = DVR::new(1, 1);
    /// assert_eq!(dvr, Err(ProofError::DVRError(1)));
    /// ```
    pub fn new(a: Identifier, b: Identifier) -> Result<Self, ProofError> {
        if is_operator(a) {
            Err(ProofError::DVRError(a))
        } else if is_operator(b) {
            Err(ProofError::DVRError(b))
        } else if a < b {
            Ok(DVR(a, b))
        } else if a > b {
            Ok(DVR(b, a))
        } else {
            Err(ProofError::DVRError(a))
        }
    }

    /// Uses the given `Substitution` to create new `DVR`s for each pair of variables in the new
    /// expressions for `self.variables()`.
    ///
    /// # Errors
    /// The `Iterator` will produce a `DVRError` if the substitutions for this `DVR`s' variables
    /// contains common variables
    ///
    /// # Example
    /// ```
    /// use attomath::dvr::DVR;
    /// use attomath::expression::{Expression, WholeSubstitution};
    /// use attomath::error::ProofError;
    ///
    /// let dvr = DVR::new(0, 1).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let expr0 = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// sub.insert(0, expr0.to_slice());
    /// let expr1 = Expression::from_raw(vec![2]).unwrap();
    /// sub.insert(1, expr1.to_slice());
    ///
    /// let mut new_dvrs = dvr.substitute(&sub).collect::<Result<Vec<_>, _>>();
    /// new_dvrs = new_dvrs.map(|mut ds| {
    ///     ds.sort();
    ///     ds.dedup();
    ///     ds
    /// });
    ///
    /// let mut expected = vec![DVR::new(0, 2).unwrap(), DVR::new(1, 2).unwrap()];
    /// expected.sort();
    /// expected.dedup();
    /// assert_eq!(new_dvrs, Ok(expected));
    ///
    /// let dvr = DVR::new(0, 1).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let expr0 = Expression::from_raw(vec![-2, 0, 1]).unwrap();
    /// sub.insert(0, expr0.to_slice());
    /// let expr1 = Expression::from_raw(vec![-2, 1, 2]).unwrap();
    /// sub.insert(1, expr1.to_slice());
    ///
    /// let new_dvrs = dvr.substitute(&sub).collect::<Result<Vec<_>, _>>();
    ///
    /// assert_eq!(new_dvrs, Err(ProofError::DVRError(1)));
    /// ```
    pub fn substitute<S: Substitution>(&self, substitution: &S) -> Iter {
        let DVR(a, b) = self;
        let vars_a = if let Some(sub) = substitution.substitution_opt(*a) {
            let mut res = sub.variables().collect::<Vec<_>>();
            res.sort();
            res.dedup();
            res
        } else {
            vec![*a]
        };
        let vars_b = if let Some(sub) = substitution.substitution_opt(*b) {
            let mut res = sub.variables().collect::<Vec<_>>();
            res.sort();
            res.dedup();
            res
        } else {
            vec![*b]
        };
        Iter {
            a: vars_a,
            b: vars_b,
            index: 0,
        }
    }

    /// Turns this dvr into its standard representation, numbering variables in the order of their
    /// apperance. And sorting this `DVR`s variables;
    ///
    /// # Example
    /// ```
    /// use attomath::dvr::DVR;
    ///
    /// let mut dvr = DVR::new(0, 2).unwrap();
    /// let mut var_map = vec![None; 6];
    /// var_map[2] = Some(3);
    /// let mut next_var = 5;
    /// dvr.standardize(&mut var_map, &mut next_var);
    /// assert_eq!(dvr, DVR::new(3, 5).unwrap());
    /// assert_eq!(var_map, vec![Some(5), None, Some(3), None, None, None]);
    /// assert_eq!(next_var, 6);
    pub fn standardize(
        &mut self,
        var_map: &mut Vec<Option<Identifier>>,
        next_var: &mut Identifier,
    ) {
        let DVR(a, b) = self;
        *a = var_map[*a as usize].unwrap_or_else(|| {
            let res = *next_var;
            *next_var += 1;
            var_map[*a as usize] = Some(res);
            res
        });
        *b = var_map[*b as usize].unwrap_or_else(|| {
            let res = *next_var;
            *next_var += 1;
            var_map[*b as usize] = Some(res);
            res
        });
        if a > b {
            let temp = *a;
            *a = *b;
            *b = temp;
        }
    }
}
