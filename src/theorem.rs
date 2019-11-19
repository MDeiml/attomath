use crate::{
    dvr::DVR,
    error::ProofError,
    statement::{is_operator, OwnedStatement, Statement},
    substitution::{Substitution, WholeSubstitution},
    types::*,
};

/// A theorem consisting of zero or more [`DVR`s](../dvr/struct.DVR.html) or _assumptions_
/// and a _conclusion_
///
/// A theorem could represent something like "if x0 is provable and (x0 -> x1) is provable then b
/// is provable". In this example the assumptions would be "x0" and "x0 -> x1" and the conclusion
/// would be "x1".
///
/// When using this struct it is guaranteed that only valid theorems can be constructed (using
/// [`substitute`](#method.substitute), [`combine`](#method.combine) and
/// [`standardize`](#method.standardize)) provided that only valid theorems (or axioms) are
/// constructed using [`new`](#method.new).
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Theorem {
    conclusion: OwnedStatement,
    assumptions: Vec<OwnedStatement>,
    dvrs: Vec<DVR>,
}

impl Theorem {
    /// Returns this theorems' conclusion
    pub fn conclusion(&self) -> &OwnedStatement {
        &self.conclusion
    }

    /// Returns this theorems' assumptions
    pub fn assumptions(&self) -> &[OwnedStatement] {
        &self.assumptions
    }

    /// Returns this theorems' `DVR`s
    pub fn dvrs(&self) -> &[DVR] {
        &self.dvrs
    }

    /// Create a new `Theorem` containig the given assumptions, `DVR`s and conclusion
    ///
    /// This should only be used for axioms and theorems that are already proven.
    pub fn new(
        conclusion: OwnedStatement,
        assumptions: Vec<OwnedStatement>,
        dvrs: Vec<DVR>,
    ) -> Self {
        Theorem {
            conclusion,
            assumptions,
            dvrs,
        }
    }

    /// Turns this theorem into its standard representation, numbering variables in the order of
    /// their apperance and sorting the assumptions and dvrs (see
    /// [`Statement::standardize`](../statement/trait.Statement.html#standardize) and
    /// [`DVR::standardize`](../dvr/struct.DVR.html#standardize))
    ///
    /// # Example
    /// ```
    /// use attomath::statement::OwnedStatement;
    /// use attomath::theorem::Theorem;
    ///
    /// let conclusion = OwnedStatement::from_raw(0, vec![3]).unwrap();
    /// let assumptions = vec![
    ///     OwnedStatement::from_raw(0, vec![10]).unwrap(),
    ///     OwnedStatement::from_raw(0, vec![-2, 10, 3]).unwrap(),
    /// ];
    /// // |- x10, |- (x10 -> x3) => x3
    /// let mut theorem1 = Theorem::new(conclusion, assumptions, vec![]);
    ///
    /// let conclusion = OwnedStatement::from_raw(0, vec![2]).unwrap();
    /// let assumptions = vec![
    ///     OwnedStatement::from_raw(0, vec![-2, 1, 2]).unwrap(),
    ///     OwnedStatement::from_raw(0, vec![1]).unwrap(),
    /// ];
    /// // |- (x1 -> x2), |- x1 => x2
    /// let mut theorem2 = Theorem::new(conclusion, assumptions, vec![]);
    /// assert!(theorem1 != theorem2);
    ///
    /// theorem1.standardize();
    /// theorem2.standardize();
    /// assert_eq!(theorem1, theorem2);
    /// ```
    pub fn standardize(&mut self) {
        let max_var = self.max_var();
        let mut var_map = vec![None; max_var as usize + 1];
        let mut next_var = 0;
        self.conclusion.standardize(&mut var_map, &mut next_var);
        for a in self.assumptions.iter_mut() {
            a.standardize(&mut var_map, &mut next_var);
        }
        for dvr in self.dvrs.iter_mut() {
            dvr.standardize(&mut var_map, &mut next_var);
        }
        self.assumptions.sort();
        self.assumptions.dedup();
        self.dvrs.sort();
        self.dvrs.dedup();
    }

    /// Returns the variable with the biggest identifier occuring in this theorem. This can be used
    /// together with
    /// [`OwnedSubstitution::with_capacity`](../substitution/struct.OwnedSubstitution.html#method.with_capacity)
    /// # Example
    /// ```
    /// use attomath::statement::OwnedStatement;
    /// use attomath::theorem::Theorem;
    ///
    /// let conclusion = OwnedStatement::from_raw(0, vec![3]).unwrap();
    /// let assumptions = vec![
    ///     OwnedStatement::from_raw(0, vec![10]).unwrap(),
    ///     OwnedStatement::from_raw(0, vec![-2, 10, 3]).unwrap(),
    /// ];
    /// // |- x10, |- (x10 -> x3) => x3
    /// let mut theorem = Theorem::new(conclusion, assumptions, vec![]);
    /// assert_eq!(theorem.max_var(), 10);
    /// ```
    pub fn max_var(&self) -> Identifier {
        *self
            .conclusion
            .expression()
            .iter()
            .chain(
                self.assumptions
                    .iter()
                    .map(|st| st.expression().iter())
                    .flatten(),
            )
            .filter(|symb| !is_operator(**symb))
            .max()
            .unwrap_or(&-1)
    }

    /// Uses the given substitution on this theorem's assumptions, dvrs and conclusion to create a
    /// new theorem. (see
    /// [`Statement::substitute`](../statement/trait.Statement.html#method.substitute) and
    /// [`DVR::substitute`](../dvr/struct.DVR.html#method.substitute))
    ///
    /// # Errors
    /// This method can return a `DVRError` if the substitution violates one of this theorem's
    /// dvrs.
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    /// use attomath::dvr::DVR;
    /// use attomath::theorem::Theorem;
    /// use attomath::substitution::WholeSubstitution;
    /// use attomath::error::ProofError;
    ///
    /// let conclusion = OwnedStatement::from_raw(0, vec![-2, 0, 2]).unwrap();
    /// let assumptions = vec![
    ///     OwnedStatement::from_raw(0, vec![-2, 1, 2]).unwrap(),
    ///     OwnedStatement::from_raw(0, vec![-2, 0, 1]).unwrap(),
    /// ];
    /// let theorem = Theorem::new(conclusion.clone(), assumptions, vec![]);
    ///
    /// let mut sub = WholeSubstitution::with_capacity(3);
    /// let expr = vec![-2, 1, 2];
    /// sub.insert(0, expr.as_slice());
    /// let new_theorem = theorem.substitute(&sub).expect("This substitution should not fail");
    ///
    /// assert_eq!(new_theorem.conclusion().expression(), vec![-2, -2, 1, 2, 2].as_slice());
    /// assert_eq!(new_theorem.assumptions()[0].expression(), vec![-2, 1, 2].as_slice());
    /// assert_eq!(new_theorem.assumptions()[1].expression(), vec![-2, -2, 1, 2, 1].as_slice());
    ///
    /// let dvrs = vec![
    ///     DVR::new(0, 1).unwrap()
    /// ];
    /// let theorem = Theorem::new(conclusion, vec![], dvrs);
    /// let res = theorem.substitute(&sub);
    /// assert_eq!(res, Err(ProofError::DVRError(1)));
    /// ```
    pub fn substitute<'a, S: Substitution<'a>>(
        &'a self,
        substitution: &'a S,
    ) -> Result<Self, ProofError> {
        self.substitute_skip_assumption(substitution, None)
    }

    fn substitute_skip_assumption<'a, S: Substitution<'a>>(
        &'a self,
        substitution: &'a S,
        skip_assumption: Option<usize>,
    ) -> Result<Self, ProofError> {
        let conclusion = self.conclusion.substitute(substitution);
        let assumptions: Vec<OwnedStatement> = self
            .assumptions
            .iter()
            .enumerate()
            .filter_map(|(i, a)| {
                if Some(i) == skip_assumption {
                    None
                } else {
                    Some(a)
                }
            })
            .map(|a| a.substitute(substitution))
            .collect();
        let dvrs: Result<Vec<DVR>, ProofError> = self
            .dvrs
            .iter()
            .map(|dvr| dvr.substitute(substitution))
            .flatten()
            .collect();
        let dvrs = dvrs?;
        Ok(Theorem {
            conclusion,
            assumptions,
            dvrs,
        })
    }

    /// Creates a new `Theorem` by applying `other` to this theorem's assumption with index `index`
    ///
    /// # Errors
    /// This can product the following errors:
    /// * `OperatorMismatch`, `VariableMismatch` or `JudgementMismatch` - if the conclusion of
    /// `other` cannot be unified with the specified assumption (see
    /// [`Statement::unify`](../statement/trait.Statement.html#method.unify))
    /// * `DVRError`- if the substitution needed to transform the conclusion of `other` into te
    /// specified assumption violates one of this theorems' `DVR`s (see
    /// [`standardize`](#method.standardize))
    /// * `ParameterError` - if `index >= self.assumptions().len()`
    ///
    /// # Example
    /// ```
    /// use attomath::theorem::Theorem;
    /// use attomath::statement::{OwnedStatement, Statement};
    ///
    /// // |- x0, |- (x0 -> x1) => |- x1
    /// let ax_mp = Theorem::new(
    ///     OwnedStatement::from_raw(0, vec![1]).unwrap(),
    ///     vec![
    ///         OwnedStatement::from_raw(0, vec![0]).unwrap(),
    ///         OwnedStatement::from_raw(0, vec![-2, 0, 1]).unwrap(),
    ///     ],
    ///     vec![],
    /// );
    ///
    /// // |- x2 => |- (x3 -> x4)
    /// let t0 = Theorem::new(
    ///     OwnedStatement::from_raw(0, vec![-2, 3, 4]).unwrap(),
    ///     vec![
    ///         OwnedStatement::from_raw(0, vec![2]).unwrap()
    ///     ],
    ///     vec![],
    /// );
    ///
    /// // |- x3, |- x2 => x4
    /// let t1 = ax_mp.combine(&t0, 1).expect("This should not fail");
    /// assert_eq!(t1.conclusion().expression(), vec![4].as_slice());
    /// assert_eq!(t1.assumptions()[0].expression(), vec![3].as_slice());
    /// assert_eq!(t1.assumptions()[1].expression(), vec![2].as_slice());
    /// ```
    pub fn combine(&self, other: &Theorem, index: usize) -> Result<Self, ProofError> {
        if index > self.assumptions.len() {
            return Err(ProofError::ParameterError(index, self.assumptions.len()));
        }
        let max_var = self.max_var();
        let mut substitution = WholeSubstitution::with_capacity(max_var as usize + 1);
        other
            .conclusion
            .unify(&self.assumptions[index], &mut substitution)?;
        let shift = other.max_var() + 1;
        let numbers = (shift..=shift + max_var as Identifier + 1).collect::<Vec<_>>();
        substitution.substitute_remaining(&numbers);
        let mut t = self.substitute_skip_assumption(&substitution, Some(index))?;
        t.assumptions.extend_from_slice(&other.assumptions);
        t.assumptions.shrink_to_fit();
        t.dvrs.extend_from_slice(&other.dvrs);
        t.dvrs.shrink_to_fit();
        Ok(t)
    }
}
