use crate::types::*;

#[derive(Debug)]
pub struct WholeSubstitution<'a> {
    substitution: Vec<Option<&'a [Identifier]>>,
}

impl<'a> WholeSubstitution<'a> {
    pub fn with_capacity(n: usize) -> Self {
        WholeSubstitution {
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

    pub fn insert(&mut self, id: Identifier, expr: &'a [Identifier]) {
        self.substitution[id as usize] = Some(expr)
    }
}

impl<'a> Substitution<'a> for WholeSubstitution<'a> {
    fn get_substitution_opt(&self, id: Identifier) -> Option<&[Identifier]> {
        self.substitution[id as usize]
    }
}

pub struct SingleSubstitution {
    pub from: Identifier,
    pub to: Identifier,
}

impl Substitution<'_> for SingleSubstitution {
    fn get_substitution_opt(&self, id: Identifier) -> Option<&[Identifier]> {
        if id == self.from {
            Some(std::slice::from_ref(&self.to))
        } else {
            None
        }
    }
}

pub trait Substitution<'a> {
    fn get_substitution_opt(&self, id: Identifier) -> Option<&[Identifier]>;

    fn get_substitution<'b>(&'a self, id: &'b Identifier) -> &'b [Identifier]
    where
        'a: 'b,
    {
        self.get_substitution_opt(*id)
            .unwrap_or(std::slice::from_ref(id))
    }
}
