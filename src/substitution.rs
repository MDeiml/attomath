use crate::{formatter::Formatter, types::*};

#[derive(Debug)]
pub struct Substitution<'a> {
    substitution: Vec<Option<&'a [Identifier]>>,
}

impl<'a> Substitution<'a> {
    // TODO: Optimize
    pub fn single_substitution(capacity: usize, to: &'a Identifier, from: &Identifier) -> Self {
        let mut substitution = Self::with_capacity(capacity);
        substitution.substitution[*from as usize] = Some(std::slice::from_ref(to));
        substitution
    }

    pub fn with_capacity(n: usize) -> Self {
        Substitution {
            substitution: vec![None; n],
        }
    }

    pub fn substitute_remaining(&mut self, other: &'a Vec<Identifier>) {
        for (n, sub) in other.iter().zip(self.substitution.iter_mut()) {
            if sub.is_none() {
                *sub = Some(std::slice::from_ref(n));
            }
        }
    }

    pub fn get_substitution(&self, id: &'a Identifier) -> &'a [Identifier] {
        self.substitution[*id as usize].unwrap_or(std::slice::from_ref(id))
    }

    pub fn get_substitution_opt(&self, id: &Identifier) -> Option<&[Identifier]> {
        self.substitution[*id as usize]
    }

    pub fn insert(&mut self, id: &Identifier, expr: &'a [Identifier]) {
        self.substitution[*id as usize] = Some(expr)
    }
}
