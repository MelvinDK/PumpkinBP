use std::collections::HashMap;

use crate::{
    engine::{AssignmentsInteger, AssignmentsPropositional},
    pumpkin_asserts::pumpkin_assert_moderate,
};

use super::{IntegerVariable, Literal, Solution};

#[derive(Clone)]
pub struct Function {
    weighted_literals: HashMap<Literal, u64>,
    weighted_integers: HashMap<IntegerVariable, u64>,
    constant_term: u64,
}

impl Function {
    pub fn new() -> Function {
        Function {
            weighted_literals: HashMap::new(),
            weighted_integers: HashMap::new(),
            constant_term: 0,
        }
    }

    pub fn add_weighted_literal(&mut self, literal: Literal, weight: u64) {
        //we want to avoid the situation where both polarities of a variable have a weight
        //  in case that happens, we keep a weight for one of the two polarity, and factor in the obligatory cost in the constant term

        let negative_literal = !literal;
        if let Some(opposite_weight) = self.weighted_literals.get_mut(&negative_literal) {
            pumpkin_assert_moderate!(*opposite_weight != 0);
            match weight.cmp(opposite_weight) {
                std::cmp::Ordering::Less => {
                    *opposite_weight -= weight;
                    self.constant_term += weight;
                }
                std::cmp::Ordering::Equal => {
                    self.weighted_literals.remove(&negative_literal);
                    self.constant_term += weight;
                }
                std::cmp::Ordering::Greater => {
                    let diff = weight - *opposite_weight;
                    self.constant_term += *opposite_weight;
                    self.weighted_literals.remove(&negative_literal);
                    self.weighted_literals.insert(literal, diff);
                }
            }
        } else {
            *self.weighted_literals.entry(literal).or_insert(0) += weight;
        }
    }

    pub fn add_weighted_integer(&mut self, integer_variable: IntegerVariable, weight: u64) {
        *self.weighted_integers.entry(integer_variable).or_insert(0) += weight;
    }

    pub fn add_constant_term(&mut self, value: u64) {
        self.constant_term += value;
    }

    pub fn get_weighted_literals(&self) -> std::collections::hash_map::Iter<Literal, u64> {
        self.weighted_literals.iter()
    }

    pub fn get_weighted_integers(&self) -> std::collections::hash_map::Iter<IntegerVariable, u64> {
        self.weighted_integers.iter()
    }

    pub fn get_constant_term(&self) -> u64 {
        self.constant_term
    }

    pub fn is_empty(&self) -> bool {
        self.weighted_integers.is_empty()
            && self.weighted_literals.is_empty()
            && self.constant_term == 0
    }

    pub fn evaluate_solution(&self, solution: &Solution) -> u64 {
        let mut value: u64 = 0;
        //add the contribution of the propositional part
        for term in self.get_weighted_literals() {
            let literal = *term.0;
            let weight = *term.1;
            value += weight * (solution.get_literal_value(literal) as u64);
        }
        //add the contribution of the integer part
        for term in self.get_weighted_integers() {
            let integer_variable = *term.0;
            let weight = *term.1;
            value += weight * solution[integer_variable] as u64;
        }
        value
    }

    pub fn evaluate_assignment(
        &self,
        assignments_propositional: &AssignmentsPropositional,
        assignments_integer: &AssignmentsInteger,
    ) -> u64 {
        let mut value: u64 = self.constant_term;
        //add the contribution of the propositional part
        for term in self.get_weighted_literals() {
            let literal = *term.0;
            let weight = *term.1;
            pumpkin_assert_moderate!(assignments_propositional.is_literal_assigned(literal));
            value += weight * (assignments_propositional.is_literal_assigned_true(literal) as u64);
        }
        //add the contribution of the integer part
        for term in self.get_weighted_integers() {
            let integer_variable = *term.0;
            let weight = *term.1;
            pumpkin_assert_moderate!(
                assignments_integer.is_integer_variable_assigned(integer_variable)
            );
            value += weight * assignments_integer.get_assigned_value(integer_variable) as u64;
        }
        value
    }
}

#[derive(Clone)]
pub struct WeightedInteger {
    pub integer_variable: IntegerVariable,
    pub weight: u64,
}
