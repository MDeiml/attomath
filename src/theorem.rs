use std::{cmp::Ordering, num::Wrapping};

use crate::{
    dvr::DVR,
    error::ProofError,
    expression::{
        is_operator, ChainSubstitution, ShiftSubstitution, Substitution, VariableSubstitution,
        WholeSubstitution,
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

        self.assumptions.sort_unstable();
        self.assumptions.dedup();

        let mut indexed_assumptions = self
            .assumptions
            .iter()
            .cloned()
            .enumerate()
            .map(|(a, b)| (b, a))
            .collect::<Vec<_>>();
        let normalized_assumptions = self
            .assumptions
            .drain(..)
            .map(|assumption| {
                let mut normalized = assumption;
                normalized.expression.standardize(
                    &mut vec![None; (Wrapping(max_var as usize) + Wrapping(1)).0],
                    &mut 0,
                );
                normalized
            })
            .collect::<Vec<_>>();
        indexed_assumptions.sort_unstable_by_key(|(_, index)| &normalized_assumptions[*index]);

        let mut temp_next_var = next_var;
        for (assumption, _) in indexed_assumptions.iter_mut() {
            assumption
                .expression
                .standardize(&mut var_map, &mut temp_next_var);
        }
        for (i, v) in var_map.iter_mut().enumerate() {
            *v = if i < next_var as usize {
                Some(i as Identifier)
            } else {
                None
            };
        }
        let mut var_maps = vec![var_map];

        for assumptions in indexed_assumptions
            .group_by_mut(|(_, i), (_, j)| normalized_assumptions[*i] == normalized_assumptions[*j])
        {
            let mut next_var1 = 0;
            let mut assumptions_min: Option<Vec<(OwnedStatement, usize)>> = None;

            let mut var_maps1 = Vec::new();
            for var_map in var_maps.iter_mut() {
                let mut perm = assumptions.iter().cloned().collect::<Vec<_>>();
                for (assumption, _) in perm.iter_mut() {
                    assumption.expression.substitute_variables(&var_map);
                }
                let mut perm = Permutations::new(&mut perm);
                while let Some(permutation) = perm.next() {
                    let mut var_map1 = var_map.clone();
                    next_var1 = next_var;

                    for (assumption, _) in permutation.iter_mut() {
                        assumption.expression.standardize_range(
                            &mut var_map1,
                            &mut next_var1,
                            next_var..,
                        );
                    }
                    match assumptions_min
                        .as_deref_mut()
                        .map(|a_min| {
                            permutation
                                .iter()
                                .map(|(a, _)| a)
                                .cmp(a_min.iter().map(|(a, _)| a))
                        })
                        .unwrap_or(Ordering::Less)
                    {
                        Ordering::Equal => {
                            var_maps1.push(var_map1);
                        }
                        Ordering::Less => {
                            var_maps1.clear();
                            var_maps1.push(var_map1);
                            assumptions_min = Some(permutation.iter().cloned().collect());
                        }
                        Ordering::Greater => {}
                    }
                }
            }
            var_maps = var_maps1;
            next_var = next_var1;
            assumptions.swap_with_slice(assumptions_min.unwrap().as_mut_slice());
        }

        // var_maps are all equal. Just take the first one
        self.assumptions
            .extend(indexed_assumptions.into_iter().map(|(a, _)| a));

        for dvr in self.dvrs.iter_mut() {
            *dvr = dvr
                .substitute(&VariableSubstitution::new(var_maps[0].as_slice()))
                .next()
                .unwrap()
                .unwrap();
        }

        self.dvrs.sort_unstable();
        self.dvrs.dedup();
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

struct Permutations<'a, T> {
    sequence: &'a mut [T],
    counters: Vec<usize>,
    depth: usize,
}

impl<'a, T> Permutations<'a, T> {
    fn new(sequence: &'a mut [T]) -> Self {
        let length = sequence.len();
        Permutations {
            sequence,
            counters: vec![0; length],
            depth: 0,
        }
    }

    fn next(&mut self) -> Option<&mut [T]> {
        if self.depth >= self.sequence.len() {
            return None;
        }
        if self.depth != 0 {
            while self.counters[self.depth] >= self.depth {
                self.counters[self.depth] = 0;
                self.depth += 1;
                if self.depth >= self.sequence.len() {
                    return None;
                }
            }
            if self.depth % 2 == 0 {
                self.sequence.swap(0, self.depth);
            } else {
                self.sequence.swap(self.counters[self.depth], self.depth);
            }
            self.counters[self.depth] += 1;
            self.depth = 1;
            Some(&mut self.sequence)
        } else {
            self.depth = 1;
            Some(&mut self.sequence)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn permutations() {
        let mut arr = [0, 1, 2, 3];
        let mut perm = Permutations::new(&mut arr);
        let mut counter = 0;
        while let Some(_) = perm.next() {
            counter += 1;
        }
        assert_eq!(counter, 24);
    }
}
