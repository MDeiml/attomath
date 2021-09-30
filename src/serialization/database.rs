use crate::{error::ProofError, expression::SingleSubstitution, Identifier, Theorem};
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
pub struct Database {
    names: HashMap<String, (usize, usize)>,
    theorems: Vec<(Theorem, Proof<usize>, Option<String>)>,
    last_name: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Proof<K> {
    Simplify(K, Identifier, Identifier),
    Combine(K, K, usize),
    Axiom(Theorem),
}

impl<K> Proof<K> {
    pub fn map_id_result<K1, F, E>(self, f: F) -> Result<Proof<K1>, E>
    where
        F: Fn(K) -> Result<K1, E>,
    {
        Ok(match self {
            Proof::Simplify(id, a, b) => Proof::Simplify(f(id)?, a, b),
            Proof::Combine(id_a, id_b, index) => Proof::Combine(f(id_a)?, f(id_b)?, index),
            Proof::Axiom(theorem) => Proof::Axiom(theorem),
        })
    }

    pub fn map_id<K1, F>(self, f: F) -> Proof<K1>
    where
        F: Fn(K) -> K1,
    {
        self.map_id_result::<_, _, ()>(|id| Ok(f(id))).unwrap()
    }
}

#[derive(Debug)]
pub enum DatabaseError {
    /// Error produced when trying to use a nonexistent theorem id (see
    /// [`Database`](../database/struct.Database.html)
    TheoremNotFound(Option<String>, Option<usize>),
    /// Error produced when trying to insert using a already used theorem id (see
    /// [`Database`](../database/struct.Database.html)
    NameCollision(String),
    TheoremMismatch(Theorem, Theorem),
    ProofError(ProofError),
}

impl From<ProofError> for DatabaseError {
    fn from(e: ProofError) -> Self {
        Self::ProofError(e)
    }
}

impl Database {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            theorems: Vec::new(),
            last_name: 0,
        }
    }

    fn get_index(&self, name: Option<&str>, index: Option<usize>) -> Result<usize, DatabaseError> {
        let (start, end) = match name {
            Some(name) => *self
                .names
                .get(name)
                .ok_or(DatabaseError::TheoremNotFound(Some(name.to_owned()), index))?,
            None => (self.last_name, self.theorems.len()),
        };
        match index {
            Some(i) => {
                if start + i < end {
                    Ok(start + i)
                } else {
                    Err(DatabaseError::TheoremNotFound(
                        name.map(|s| s.to_owned()),
                        index,
                    ))
                }
            }
            None => {
                if start == end {
                    Err(DatabaseError::TheoremNotFound(
                        name.map(|s| s.to_owned()),
                        index,
                    ))
                } else {
                    Ok(end - 1)
                }
            }
        }
    }

    pub fn get(&self, name: Option<&str>, index: Option<usize>) -> Result<&Theorem, DatabaseError> {
        Ok(&self.theorems[self.get_index(name, index)?].0)
    }

    pub fn add_name(&mut self, name: String) -> Result<(), DatabaseError> {
        if self.theorems.is_empty() {
            return Err(DatabaseError::TheoremNotFound(None, Some(0)));
        }
        let index = self.theorems.len() - 1;
        if self.theorems[index].2.is_some() {
            return Err(DatabaseError::TheoremNotFound(None, None));
        }
        match self.names.entry(name.clone()) {
            std::collections::hash_map::Entry::Occupied(_) => {
                Err(DatabaseError::NameCollision(name))
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                &entry.insert((self.last_name, index + 1));
                self.last_name = index + 1;
                self.theorems[index].2 = Some(name.to_owned());
                Ok(())
            }
        }
    }

    pub fn add_proof<'a>(
        &'a mut self,
        proof: Proof<(Option<String>, Option<usize>)>,
    ) -> Result<&'a Theorem, DatabaseError> {
        let proof = proof.map_id_result(|id| self.get_index(id.0.as_deref(), id.1))?;
        let new_theorem = match proof {
            Proof::Simplify(id, a, b) => {
                let theorem = &self.theorems[id].0;
                let mut new_theorem =
                    theorem.substitute(&SingleSubstitution::new(a, b).unwrap())?;
                new_theorem.standardize();
                new_theorem
            }
            Proof::Combine(id_a, id_b, index) => {
                let theorem_a = &self.theorems[id_a].0;
                let theorem_b = &self.theorems[id_b].0;
                let mut new_theorem = theorem_a.combine(&theorem_b, index)?;
                new_theorem.standardize();
                new_theorem
            }
            Proof::Axiom(ref theorem) => theorem.clone(),
        };
        self.theorems.push((new_theorem, proof, None));
        Ok(&self.theorems.last().unwrap().0)
    }

    pub fn substitute(&mut self, theorem: Theorem) -> Result<(), DatabaseError> {
        let last = &mut self
            .theorems
            .last_mut()
            .ok_or(DatabaseError::TheoremNotFound(None, None))?
            .0;
        let mut theorem_standardized = theorem.clone();
        theorem_standardized.standardize();
        if last == &theorem_standardized {
            *last = theorem;
            Ok(())
        } else {
            Err(DatabaseError::TheoremMismatch(theorem, last.clone()))
        }
    }

    fn reverse_id(&self, id: usize, current_id: usize) -> (Option<&str>, Option<usize>) {
        if let Some(name) = &self.theorems[id].2 {
            (Some(name), None)
        } else if id == current_id - 1 {
            (None, None)
        } else if id >= self.last_name {
            (None, Some(id - self.last_name))
        } else {
            let name = self.theorems[id..]
                .iter()
                .filter_map(|x| x.2.as_ref())
                .next()
                .unwrap();
            let (start, end) = self.names[name];
            if end >= current_id {
                (None, Some(id - start))
            } else {
                (Some(name), Some(id - start))
            }
        }
    }

    pub fn proofs<'a>(
        &'a self,
    ) -> impl 'a + Iterator<Item = (&Theorem, Proof<(Option<&str>, Option<usize>)>, Option<&str>)>
    {
        self.theorems
            .iter()
            .enumerate()
            .map(move |(current_id, (theorem, proof, name))| {
                let proof = proof.clone().map_id(|id| self.reverse_id(id, current_id));
                (theorem, proof, name.as_deref())
            })
    }
}
