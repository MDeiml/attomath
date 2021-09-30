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

/// A theorem consisting of zero or more [`DVR`] or __assumptions__
/// and a __conclusion__
///
/// A theorem could represent something like _if x0 is provable and (x0 -> x1) is provable then b
/// is provable_. In this example the assumptions would be _x0_ and _x0 -> x1_ and the conclusion
/// would be _x1_.
///
/// When using this struct it is guaranteed that only valid theorems can be constructed (using
/// [`Theorem::substitute`], [`Theorem::combine`] and [`Theorem::standardize`]) provided that only valid theorems (or axioms)
/// are constructed using [`Theorem::new`].
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
    /// [`Expression::standardize`][crate::Expression::standardize]).
    ///
    /// It holds, that applying standardize twice is the same as applying it once. Two theorems are
    /// logically "equal", that is they can be constructed from each other by reordering
    /// assumptions and substituting variables by mutally distinct variables, if and only if they
    /// are the same after calling standardize on them.
    pub fn standardize(&mut self) {
        let max_var = self.max_var();
        let mut var_map = vec![None; (Wrapping(max_var as usize) + Wrapping(1)).0];
        let mut next_var = 0;

        // first number the variables of the conclusion in order
        self.conclusion
            .expression
            .standardize(&mut var_map, &mut next_var);

        // remove duplicate assumptions
        // TODO: maybe move this into combine / simplify
        self.assumptions.sort_unstable();
        self.assumptions.dedup();

        // calculate a "normalized" version for each assumption. That is, number each single
        // theorems variables in order
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
        // sort the assumptions by their normalized version. Assumptions with the same
        // normalization are now grouped together
        indexed_assumptions.sort_unstable_by_key(|(_, index)| &normalized_assumptions[*index]);

        // The rest of this function is to find for each group of the same normalization the
        // variable substitution (some variables could be fixed by previous groups) that results
        // in the smallest lexicographic ordering of the group after its elements are sorted

        // first standardize all assumptions in their new order, so for each group the "free"
        // variables are going to be substituted by some permutation of themselves
        let mut temp_next_var = next_var;
        for (assumption, _) in indexed_assumptions.iter_mut() {
            assumption
                .expression
                .standardize(&mut var_map, &mut temp_next_var);
        }

        // we have to forget the variable map we just computed, but not the variables that are also
        // part of the conclusion. But these are now numbered 0 .. next_var and do not have to be
        // changed any longer.
        for (i, v) in var_map.iter_mut().enumerate() {
            *v = if i < next_var as usize {
                Some(i as Identifier)
            } else {
                None
            };
        }
        // var_maps holds the current candidates for the variable substitution that results in the
        // lowest lexicographic ordering
        let mut var_maps = vec![var_map];

        for assumptions in indexed_assumptions
            .group_by_mut(|(_, i), (_, j)| normalized_assumptions[*i] == normalized_assumptions[*j])
        {
            let mut next_var1 = 0;
            let mut assumptions_min: Option<Vec<(OwnedStatement, usize)>> = None;

            // for each new group and each candidate in var_maps try all permutation of "new"
            // variables, i.e. variables that have are not yet determined in the candidates.
            // Save the best permutations in var_maps1 as the new candidates for the next iteration
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
            // save the minimal substitution in indexed_assumptions. This way we do not have to
            // substitute again with some candidate (*)
            assumptions.swap_with_slice(assumptions_min.unwrap().as_mut_slice());
        }

        // just use the saved assumptions (*) this is equivalent to every substitution candidate
        self.assumptions
            .extend(indexed_assumptions.into_iter().map(|(a, _)| a));

        // every variable in a DVR has to appear in some assumption or the conclusion. Just order
        // the DVRs accordingly.
        for dvr in self.dvrs.iter_mut() {
            *dvr = dvr
                .substitute(&VariableSubstitution::new(var_maps[0].as_slice()).unwrap())
                .next()
                .unwrap()
                .unwrap();
        }

        self.dvrs.sort_unstable();
        self.dvrs.dedup();
    }

    /// Returns the variable with the biggest identifier occuring in this theorem. This can be used
    /// together with [`WholeSubstitution::with_capacity`].
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
    /// new theorem. (see [`Statement::substitute`][crate::Statement::substitute], [`DVR::substitute`])
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
    /// [`Statement::unify`][crate::Statement::unify])
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
