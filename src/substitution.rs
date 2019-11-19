use crate::types::*;

/// A general [`Substitution`](trait.Substitution.html)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WholeSubstitution<'a> {
    substitution: Vec<Option<&'a [Identifier]>>,
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
    /// use attomath::substitution::{Substitution, WholeSubstitution};
    ///
    /// let expr = vec![-2, 0, 1];
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.as_slice());
    /// let rem = vec![2, 3];
    /// sub.substitute_remaining(rem.as_slice());
    /// assert_eq!(sub.substitution_opt(0), Some(expr.as_slice()));
    /// assert_eq!(sub.substitution_opt(1), Some(std::slice::from_ref(&3)));
    /// ```
    pub fn substitute_remaining(&mut self, other: &'a [Identifier]) {
        for (n, sub) in other.iter().zip(self.substitution.iter_mut()) {
            if sub.is_none() {
                *sub = Some(std::slice::from_ref(n));
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
    /// use attomath::substitution::{Substitution, WholeSubstitution};
    ///
    /// let expr = vec![-2, 0, 1];
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.as_slice());
    /// assert_eq!(sub.substitution_opt(0), Some(expr.as_slice()));
    /// assert_eq!(sub.substitution_opt(1), None);
    /// ```
    pub fn insert(&mut self, id: Identifier, expr: &'a [Identifier]) {
        self.substitution[id as usize] = Some(expr)
    }
}

impl<'a> Substitution<'a> for WholeSubstitution<'a> {
    fn substitution_opt(&self, id: Identifier) -> Option<&[Identifier]> {
        self.substitution[id as usize]
    }

    fn max_var(&self) -> Identifier {
        self.substitution.len() as i16 - 1
    }
}

/// A 1:1 [`Substitution`](trait.Substitution.html) for a single variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleSubstitution {
    from: Identifier,
    to: Identifier,
}

impl SingleSubstitution {
    /// Creates a new `SingleSubstitution` substituting `from` with `to`.
    ///
    /// # Example
    /// ```
    /// use attomath::substitution::{Substitution, SingleSubstitution};
    ///
    /// let sub = SingleSubstitution::new(2, 3);
    /// assert_eq!(sub.substitution_opt(0), None);
    /// assert_eq!(sub.substitution_opt(2), Some(std::slice::from_ref(&3)));
    /// ```
    pub fn new(from: Identifier, to: Identifier) -> Self {
        SingleSubstitution { from, to }
    }
}

impl Substitution<'_> for SingleSubstitution {
    fn substitution_opt(&self, id: Identifier) -> Option<&[Identifier]> {
        if id == self.from {
            Some(std::slice::from_ref(&self.to))
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
/// This is intented to be used together with [`Statement`s](../statement/trait.Statement.html).
pub trait Substitution<'a> {
    /// Get the stored substitution for the variable with identifier `id`. Or `None` if the
    /// variable should not be replaced.
    ///
    /// # Panics
    /// This may panic if `id` is not in the range `0..=self.max_var()`.
    ///
    /// # Example
    /// ```
    /// use attomath::substitution::{Substitution, WholeSubstitution};
    ///
    /// let expr = vec![-2, 0, 1];
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.as_slice());
    /// assert_eq!(sub.substitution_opt(0), Some(expr.as_slice()));
    /// assert_eq!(sub.substitution_opt(1), None);
    /// ```
    fn substitution_opt(&self, id: Identifier) -> Option<&[Identifier]>;

    /// Get the maximum variable id that can be stored in this substitution.
    ///
    /// # Example
    /// ```
    /// use attomath::substitution::{WholeSubstitution, SingleSubstitution, Substitution};
    ///
    /// let sub = WholeSubstitution::with_capacity(20);
    /// assert_eq!(sub.max_var(), 19);
    ///
    /// let sub = SingleSubstitution::new(4, 10);
    /// assert_eq!(sub.max_var(), 4);
    /// ```
    fn max_var(&self) -> Identifier;

    /// Get the stored substitution for the variable with identifier `id`. Returns `[id]` if the
    /// variable should not be replaced
    ///
    /// # Panics
    /// This may panic if `id` is not in the range `0..=self.max_var()`.
    ///
    /// # Example
    /// ```
    /// use attomath::substitution::{WholeSubstitution, Substitution};
    ///
    /// let expr = vec![-2, 0, 1];
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// sub.insert(0, expr.as_slice());
    /// assert_eq!(sub.substitution(&0), expr.as_slice());
    /// assert_eq!(sub.substitution(&1), std::slice::from_ref(&1));
    /// ```
    fn substitution<'b>(&'a self, id: &'b Identifier) -> &'b [Identifier]
    where
        'a: 'b,
    {
        self.substitution_opt(*id)
            .unwrap_or(std::slice::from_ref(id))
    }
}
