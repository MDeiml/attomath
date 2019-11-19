use crate::{
    error::ProofError,
    substitution::{Substitution, WholeSubstitution},
    types::*,
};

/// [`Statement`](trait.Statement.html) owning its data
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
pub struct OwnedStatement {
    judgement: Judgement,
    expression: Box<[Identifier]>,
}

impl Statement for OwnedStatement {
    fn judgement(&self) -> Judgement {
        self.judgement
    }

    fn expression<'a>(&'a self) -> &'a [Identifier] {
        &self.expression
    }
}

impl OwnedStatement {
    /// Create a statement form raw data. Returns `None` if the data is not a valid statement.
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    ///
    /// let s = OwnedStatement::from_raw(0, vec![-2, -3, 1]);
    /// assert!(s.is_none());
    /// let s = OwnedStatement::from_raw(0, vec![-2, 0, 1]);
    /// assert!(s.is_some());
    /// ```
    pub fn from_raw(judgement: Judgement, expression: Vec<Identifier>) -> Option<Self> {
        if (judgement, expression.as_slice()).check() {
            Some(OwnedStatement {
                judgement,
                expression: expression.into_boxed_slice(),
            })
        } else {
            None
        }
    }

    /// Turns this statement into its standard representation, numbering variables in the order of
    /// their apperance.
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    ///
    /// let mut s = OwnedStatement::from_raw(0, vec![-2, -2, 2, 0, 2]).unwrap();
    /// let mut var_map = vec![None; 6];
    /// var_map[2] = Some(3);
    /// let mut next_var = 5;
    /// s.standardize(&mut var_map, &mut next_var);
    /// assert_eq!(s.expression(), &[-2, -2, 3, 5, 3]);
    /// assert_eq!(var_map, vec![Some(5), None, Some(3), None, None, None]);
    /// assert_eq!(next_var, 6);
    /// ```
    pub fn standardize(
        &mut self,
        var_map: &mut Vec<Option<Identifier>>,
        next_var: &mut Identifier,
    ) {
        for symb in self.expression.iter_mut() {
            if !is_operator(*symb) {
                *symb = var_map[*symb as usize].unwrap_or_else(|| {
                    let var = *next_var;
                    var_map[*symb as usize] = Some(var);
                    *next_var += 1;
                    var
                });
            }
        }
    }
}

impl<'a> Statement for (Judgement, &'a [Identifier]) {
    fn judgement(&self) -> Judgement {
        self.0
    }

    fn expression<'b>(&'b self) -> &'b [Identifier] {
        self.1
    }
}

/// A a combination of a judgement and an expression, e.g. _x0 -> x0 is provable_
///
/// The __judgement__ is given in form of an integer, but often represents some meaning, like _this
/// expression is provable_ or _this expression is syntactically correct_.
///
/// The __expression__ is a sequence of integers, with the following meaning:
/// * A non-negative integer stands for a __variable__ uniquely identified by this integer
/// * A integer less or equal to `-2` stands for an __operator__. The operator has no associated
/// meaning in this context, but in a normal usecase could represent some expression or operation,
/// e.g. an implication or an addition
/// * The integer `-1` is a __special constant__ node to be used for operators with arity 0 or 1
///
/// A valid expression must have of one of the following formats:
/// * A __variable__, or the __special constant__ `-1`
/// * A __operator__, followed by two valid expression (the operands)
///
/// For example a valid sequences would be `[-2, 0, -2, 1, 0]` or `[-3, -2, 0, 0, -1]` which could
/// stand for _x0 -> (x1 -> x0)_ or _not (x0 -> x0)_ respectively.
///
/// To create operators of arity 0 and 1, one can use the __special constant__ `-1`. For example
/// `-2, 0, -1` is a valid expression which could stand for _not x0_.
///
/// To create operators of arity 3 or higher, one can split the up into multiple operators of artiy
/// 2.
/// For example `-2, 0, -3, 1, 2` is a valid sequence which could stand for _if x0 then x1 else x2_
pub trait Statement {
    /// Returns this statements' judgement
    fn judgement<'a>(&'a self) -> Judgement;

    /// Returns this statements' expression
    fn expression<'a>(&'a self) -> &'a [Identifier];

    /// Checks wether this is a valid expression
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    ///
    /// let expr = [-2i16, 0, 0];
    /// assert!((0u16, &expr[..]).check());
    /// let expr = [-2i16, 0];
    /// assert!(!(0u16, &expr[..]).check());
    /// ```
    fn check(&self) -> bool {
        self.subexpression(0).map(|s| s.len()) == Some(self.expression().len())
    }

    /// Returns the subexpression beginning at the given index or `None`, if this expression is not
    /// well formated.
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    ///
    /// let st = OwnedStatement::from_raw(0, vec![-2, 0, -2, 1, 0]).unwrap();
    /// assert_eq!(st.subexpression(2), Some(vec![-2, 1, 0].as_slice()));
    /// assert_eq!(st.subexpression(3), Some(vec![1].as_slice()));
    fn subexpression<'a>(&'a self, start_index: usize) -> Option<&'a [Identifier]> {
        let expr = self.expression();
        let mut depth = 1;
        for (i, &s) in expr[start_index..].iter().enumerate() {
            if is_operator(s) && s != -1 {
                depth += 1;
            } else {
                depth -= 1;
            }
            if depth == 0 {
                return Some(&expr[start_index..=start_index + i]);
            }
        }
        None
    }

    /// Calculates a `Substitution` which transforms `other` into `this`.
    ///
    /// # Errors
    /// * JudgementMismatch - if `self.judgement() != other.judgement`
    /// * OperatorMismatch - if the operators of `other` do not match the corresponding operators
    /// of `self`
    /// * VariableMismatch - if a variable in `other` would have to be substituted by two different
    /// expressions
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    /// use attomath::substitution::WholeSubstitution;
    /// use attomath::error::ProofError;
    ///
    /// let a = OwnedStatement::from_raw(0, vec![-2, 0, -2, 1, 0]).unwrap();
    /// let b = OwnedStatement::from_raw(0, vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub); // (x0 ~> x0, x1 ~> (x1 -> x0))
    /// assert_eq!(result, Ok(()));
    /// assert_eq!(b.substitute(&sub), a);
    ///
    /// let a = OwnedStatement::from_raw(0, vec![-2, 0, -2, 1, 0]).unwrap();
    /// let b = OwnedStatement::from_raw(0, vec![-2, 0, 0]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub); // (x0 ~> x0, x0 ~> (x1 -> x0))
    /// assert_eq!(result, Err(ProofError::VariableMismatch(
    ///     0,
    ///     vec![0].into_boxed_slice(),
    ///     vec![-2, 1, 0].into_boxed_slice(),
    /// )));
    ///
    /// let a = OwnedStatement::from_raw(0, vec![-3, 0, -2, 1, 0]).unwrap();
    /// let b = OwnedStatement::from_raw(0, vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub);
    /// assert_eq!(result, Err(ProofError::OperatorMismatch(-3, -2)));
    ///
    /// let a = OwnedStatement::from_raw(1, vec![-2, 0, -2, 1, 0]).unwrap();
    /// let b = OwnedStatement::from_raw(0, vec![-2, 0, 0]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let result = a.unify(&b, &mut sub);
    /// assert_eq!(result, Err(ProofError::JudgementMismatch(1, 0)));
    /// ```
    fn unify<'a>(
        &'a self,
        other: &Self,
        substitution: &mut WholeSubstitution<'a>,
    ) -> Result<(), ProofError> {
        if self.judgement() != other.judgement() {
            return Err(ProofError::JudgementMismatch(
                self.judgement(),
                other.judgement(),
            ));
        }
        let expr = self.expression();
        let mut expr_iter = expr.iter();
        let mut expr_index = 0;
        for &symb in other.expression().iter() {
            if is_operator(symb) {
                let symb_self = *expr_iter
                    .next()
                    .expect(format!("self is not well formated {:?}", expr).as_str());
                expr_index += 1;
                if symb_self != symb {
                    return Err(ProofError::OperatorMismatch(symb_self, symb));
                }
            } else {
                if let Some(old) = substitution.substitution_opt(symb) {
                    let start = expr_index;
                    expr_index += old.len();
                    if expr.len() < expr_index || old != &expr[start..expr_index] {
                        return Err(ProofError::VariableMismatch(
                            symb,
                            Box::from(old),
                            Box::from(
                                self.subexpression(start)
                                    .expect("self is not well formated"),
                            ),
                        ));
                    }
                    for _ in 0..old.len() {
                        expr_iter.next();
                    }
                } else {
                    let slice = self
                        .subexpression(expr_index)
                        .expect("self is not well formated");
                    expr_index += slice.len();
                    for _ in 0..slice.len() {
                        expr_iter.next();
                    }
                    substitution.insert(symb, slice);
                }
            }
        }
        return Ok(());
    }

    /// Use the given substitution on this expression to create a new expression
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    /// use attomath::substitution::WholeSubstitution;
    ///
    /// let a = OwnedStatement::from_raw(0, vec![-2, 0, 1]).unwrap();
    /// let mut sub = WholeSubstitution::with_capacity(2);
    /// let expr = [-2, 0, 1];
    /// sub.insert(0, &expr);
    /// assert_eq!(a.substitute(&sub).expression(), &[-2, -2, 0, 1, 1]);
    /// ```
    fn substitute<'a, S: Substitution<'a>>(&self, substitution: &'a S) -> OwnedStatement {
        let expr = self.expression();
        let mut new_expr = Vec::with_capacity(expr.len());
        for &symb in expr.iter() {
            if is_operator(symb) {
                new_expr.push(symb)
            } else {
                new_expr.extend_from_slice(substitution.substitution(&symb));
            }
        }
        OwnedStatement {
            judgement: self.judgement(),
            expression: new_expr.into_boxed_slice(),
        }
    }

    /// Calculates bounds (`low`, `high`) so that all statements `other` that match
    /// `self` (meaning `other.unify(&self, &mut sub)` succeds) satisfy
    /// `low <= other && other < high`
    ///
    /// # Example
    /// ```
    /// use attomath::statement::{OwnedStatement, Statement};
    ///
    /// let a = OwnedStatement::from_raw(0, vec![-2, 0, 1]).unwrap();
    /// let b = OwnedStatement::from_raw(0, vec![-2, 0, -2, 1, 0]).unwrap();
    /// let (low, high) = a.match_bounds();
    /// assert!(b >= low);
    /// assert!(b < high);
    /// ```
    fn match_bounds(&self) -> (OwnedStatement, OwnedStatement) {
        let expr = self.expression();
        let index = expr
            .iter()
            .position(|s| !is_operator(*s))
            .unwrap_or(expr.len());
        if index == 0 {
            (
                OwnedStatement {
                    judgement: self.judgement(),
                    expression: Vec::new().into_boxed_slice(),
                },
                OwnedStatement {
                    judgement: self.judgement() + 1,
                    expression: Vec::new().into_boxed_slice(),
                },
            )
        } else {
            let low = OwnedStatement {
                judgement: self.judgement(),
                expression: Box::from(&expr[0..index]),
            };
            let mut high = OwnedStatement {
                judgement: self.judgement(),
                expression: Box::from(&expr[0..index]),
            };
            high.expression[index - 1] += 1;
            (low, high)
        }
    }
}

/// Tests whether the given identifier is an operator
///
/// # Example
/// ```
/// use attomath::statement::is_operator;
///
/// assert!(is_operator(-2));
/// assert!(is_operator(-1));
/// assert!(!is_operator(0));
/// ```
pub fn is_operator(x: Identifier) -> bool {
    x < 0
}
