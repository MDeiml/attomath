use std::num::Wrapping;

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
    /// [`Expression::standardize`](../expression/struct.Expression.html#method.standardize) and
    /// [`DVR::standardize`](../dvr/struct.DVR.html#method.standardize))
    pub fn standardize(&mut self) {
        let max_var = self.max_var();
        let mut var_map = vec![None; (Wrapping(max_var as usize) + Wrapping(1)).0];
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

    pub fn is_variable_substitution(&self, other: &Self) -> bool {
        let max_var = self.max_var();
        let mut var_map = vec![None; (Wrapping(max_var as usize) + Wrapping(1)).0];
        if self.assumptions.len() != other.assumptions.len()
            || self.dvrs.len() != other.dvrs.len()
            || self.conclusion.judgement != other.conclusion.judgement
        {
            return false;
        }
        if !self
            .conclusion
            .expression
            .is_variable_substitution(&other.conclusion.expression, &mut var_map)
        {
            return false;
        }

        if !self.assumptions.is_empty() {
            let mut perm = Permutations::new(self.assumptions.len());
            let mut success = false;
            while let Some(p) = perm.next() {
                let mut inner_success = true;
                let mut var_map_temp = var_map.clone();
                for i in 0..self.assumptions.len() {
                    if !self.assumptions[i].expression.is_variable_substitution(
                        &other.assumptions[p[i]].expression,
                        &mut var_map_temp,
                    ) || self.assumptions[i].judgement != other.assumptions[p[i]].judgement
                    {
                        inner_success = false;
                        break;
                    }
                }
                if inner_success {
                    'outer: for i in 0..var_map.len() {
                        for j in 0..i {
                            if var_map_temp[i].is_some() && var_map_temp[i] == var_map_temp[j] {
                                inner_success = false;
                                break 'outer;
                            }
                        }
                    }
                }
                if inner_success {
                    success = true;
                    var_map = var_map_temp;
                    break;
                }
            }
            if !success {
                return false;
            }
        }

        if !self.dvrs.is_empty() {
            let mut perm = Permutations::new(self.dvrs.len());
            let mut success = false;
            while let Some(p) = perm.next() {
                let mut inner_success = true;
                for i in 0..self.dvrs.len() {
                    if !self.dvrs[i].is_variable_substitution(&other.dvrs[p[i]], &var_map) {
                        inner_success = false;
                        break;
                    }
                }
                if inner_success {
                    success = true;
                    break;
                }
            }
            if !success {
                return false;
            }
        }

        true
    }

    /// Returns the variable with the biggest identifier occuring in this theorem. This can be used
    /// together with
    /// [`WholeSubstitution::with_capacity`](../expression/struct.WholeSubstitution.html#method.with_capacity)
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
    /// [`Statement::substitute`](../statement/struct.Statement.html#method.substitute) and
    /// [`DVR::substitute`](../dvr/struct.DVR.html#method.substitute))
    ///
    /// This function and the functions it calls are the only ones, that need to be trusted to be
    /// sure, that only provable theorems can be proven.
    ///
    /// # Errors
    /// This method can return a `DVRError` if the substitution violates one of this theorem's
    /// `DVR`s.
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
    /// # Panics
    /// This may panic if `index > self.assumptions().len`
    ///
    /// # Errors
    /// This can product the following errors:
    /// * `OperatorMismatch`, `VariableMismatch` or `JudgementMismatch` - if the conclusion of
    /// `other` cannot be unified with the specified assumption (see
    /// [`Statement::unify`](../statement/struct.Statement.html#method.unify))
    /// * `DVRError`- if the substitution needed to transform the conclusion of `other` into the
    /// specified assumption violates one of this theorems' `DVR`s
    ///
    pub fn combine(&self, other: &Theorem, index: usize) -> Result<Self, ProofError> {
        let max_var = self.max_var();
        let mut substitution =
            WholeSubstitution::with_capacity((Wrapping(max_var as usize) + Wrapping(1)).0);
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

struct Permutations {
    length: usize,
    counters: Vec<usize>,
    depth: usize,
    next: Vec<usize>,
}

impl Permutations {
    fn new(length: usize) -> Self {
        Permutations {
            length,
            counters: vec![0; length],
            depth: 0,
            next: (0..length).collect(),
        }
    }

    fn next(&mut self) -> Option<&[usize]> {
        if self.depth >= self.length {
            return None;
        }
        if self.depth != 0 {
            while self.counters[self.depth] >= self.depth {
                self.counters[self.depth] = 0;
                self.depth += 1;
                if self.depth >= self.length {
                    return None;
                }
            }
            if self.depth % 2 == 0 {
                let temp = self.next[0];
                self.next[0] = self.next[self.depth];
                self.next[self.depth] = temp;
            } else {
                let temp = self.next[self.counters[self.depth]];
                self.next[self.counters[self.depth]] = self.next[self.depth];
                self.next[self.depth] = temp;
            }
            self.counters[self.depth] += 1;
            self.depth = 1;
            Some(&self.next)
        } else {
            self.depth = 1;
            Some(&self.next)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn permutations() {
        let mut perm = Permutations::new(4);
        let mut counter = 0;
        while let Some(_) = perm.next() {
            counter += 1;
        }
        assert_eq!(counter, 24);
    }
}
