use crate::{
    dvr::DVR,
    error::ProofError,
    expression::{
        is_operator, ChainSubstitution, ShiftSubstitution, Substitution, WholeSubstitution,
    },
    statement::OwnedStatement,
    types::*,
};

/// A theorem consisting of zero or more [`DVR`s](../dvr/struct.DVR.html) or __assumptions__
/// and a __conclusion__
///
/// A theorem could represent something like _if x0 is provable and (x0 -> x1) is provable then b
/// is provable_. In this example the assumptions would be _x0_ and _x0 -> x1_ and the conclusion
/// would be _x1_.
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
    pub fn standardize(&mut self) {
        let max_var = self.max_var();
        let mut var_map = vec![None; max_var as usize + 1];
        let mut next_var = 0;
        self.conclusion
            .expression
            .standardize(&mut var_map, &mut next_var);
        for a in self.assumptions.iter_mut() {
            a.expression.standardize(&mut var_map, &mut next_var);
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
    pub fn max_var(&self) -> Identifier {
        self.conclusion
            .expression
            .variables()
            .chain(
                self.assumptions
                    .iter()
                    .map(|st| st.expression.variables())
                    .flatten(),
            )
            .filter(|symb| !is_operator(*symb))
            .max()
            .unwrap_or(-1)
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
    pub fn substitute<S: Substitution>(&self, substitution: &S) -> Result<Self, ProofError> {
        self.substitute_skip_assumption(substitution, None)
    }

    fn substitute_skip_assumption<S: Substitution>(
        &self,
        substitution: &S,
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
        let dvrs = self
            .dvrs
            .iter()
            .map(|dvr| dvr.substitute(substitution))
            .flatten()
            .collect::<Result<Vec<_>, _>>()?;
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
        let shift_sub = ShiftSubstitution::new(shift);
        let substitution = ChainSubstitution {
            first: substitution,
            then: shift_sub,
        };
        let mut t = self.substitute_skip_assumption(&substitution, Some(index))?;
        t.assumptions.extend_from_slice(&other.assumptions);
        t.assumptions.shrink_to_fit();
        t.dvrs.extend_from_slice(&other.dvrs);
        t.dvrs.shrink_to_fit();
        Ok(t)
    }
}
