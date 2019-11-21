use crate::{
    dvr::DVR,
    expression::{is_operator, Expression},
    statement::Statement,
    theorem::Theorem,
    types::*,
};
use std::borrow::Borrow;

/// ```
/// use attomath::formatter::{StandardFormatter, Formatter};
/// use attomath::expression::Expression;
/// use attomath::theorem::Theorem;
/// use attomath::statement::Statement;
///
/// let fmt = StandardFormatter {
///     operators: vec![("->".to_owned(), false)],
///     judgements: vec!["|-".to_owned()]
/// };
/// let conclusion = Statement {
///     judgement: 0,
///     expression: Expression::from_raw(vec![1].into_boxed_slice()).unwrap()
/// };
/// let assumptions = vec![
///     Statement {
///         judgement: 0,
///         expression: Expression::from_raw(vec![0].into_boxed_slice()).unwrap(),
///     },
///     Statement {
///         judgement: 0,
///         expression: Expression::from_raw(vec![-2, 0, 1].into_boxed_slice()).unwrap(),
///     }
/// ];
/// let theorem = Theorem::new(conclusion, assumptions, vec![]);
/// assert_eq!(fmt.format_theorem(&theorem), "|- x0, |- (x0 -> x1) => |- x1");
/// ```
pub struct StandardFormatter {
    pub operators: Vec<(String, bool)>,
    pub judgements: Vec<String>,
}

impl Formatter for StandardFormatter {
    fn format_operator(&self, id: Identifier, left: String, right: String) -> String {
        let (symb, unary) = self.operators[(-id - 2) as usize].clone();
        if unary {
            format!("({} {})", symb, left)
        } else {
            format!("({} {} {})", left, symb, right)
        }
    }

    fn format_judgement(&self, judgement: Judgement) -> String {
        self.judgements[judgement as usize].to_owned()
    }
}

pub trait Formatter {
    fn format_operator(&self, id: Identifier, left: String, right: String) -> String;
    fn format_judgement(&self, judgement: Judgement) -> String;

    fn format_variable(&self, id: Identifier) -> String {
        format!("x{}", id)
    }

    fn combine_theorem(
        &self,
        dvrs: Vec<String>,
        assumptions: Vec<String>,
        conclusion: String,
    ) -> String {
        let pre = dvrs
            .iter()
            .chain(assumptions.iter())
            .fold(None, |acc: Option<String>, s| {
                let mut acc = acc
                    .map(|mut s| {
                        s.push_str(", ");
                        s
                    })
                    .unwrap_or_else(|| String::new());
                acc.push_str(s.as_str());
                Some(acc)
            });
        if let Some(pre) = pre {
            format!("{} => {}", pre, conclusion)
        } else {
            conclusion
        }
    }

    fn combine_dvr(&self, variable1: String, variable2: String) -> String {
        format!("{} <> {}", variable1, variable2)
    }

    fn combine_statement(&self, judgement: String, expression: String) -> String {
        format!("{} {}", judgement, expression)
    }

    fn format_expression<T: Borrow<[Identifier]> + std::fmt::Debug>(
        &self,
        expression: &Expression<T>,
    ) -> String {
        let id = expression.to_slice().data()[0];
        if is_operator(id) {
            let left = expression.subexpression(1);
            let right = expression.subexpression(1 + left.data().len());
            self.format_operator(
                id,
                self.format_expression(&left),
                self.format_expression(&right),
            )
        } else {
            self.format_variable(id)
        }
    }

    fn format_statement<T: Borrow<[Identifier]> + std::fmt::Debug>(
        &self,
        statement: &Statement<T>,
    ) -> String {
        self.combine_statement(
            self.format_judgement(statement.judgement),
            self.format_expression(&statement.expression),
        )
    }

    fn format_dvr(&self, dvr: &DVR) -> String {
        let (a, b) = dvr.variables();
        self.combine_dvr(self.format_variable(a), self.format_variable(b))
    }

    fn format_theorem(&self, theorem: &Theorem) -> String {
        let dvrs = theorem
            .dvrs()
            .iter()
            .map(|dvr| self.format_dvr(dvr))
            .collect::<Vec<_>>();
        let assumptions = theorem
            .assumptions()
            .iter()
            .map(|st| self.format_statement(st))
            .collect::<Vec<_>>();
        self.combine_theorem(
            dvrs,
            assumptions,
            self.format_statement(theorem.conclusion()),
        )
    }
}
