use super::super::super::{BusMappingLookup, Constraint, FixedLookup, Lookup};
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

#[derive(Clone, Debug)]
pub struct ConstraintBuilder<F> {
    pub expressions: Vec<Expression<F>>,
    pub(crate) lookups: Vec<Lookup<F>>,
    pub stack_offset: i32,
    pub call_id: Option<Expression<F>>,
}

impl<F: FieldExt> ConstraintBuilder<F> {
    pub(crate) fn with_call_id(call_id: Expression<F>) -> Self {
        Self::init(Some(call_id))
    }

    pub(crate) fn default() -> Self {
        Self::init(None)
    }

    fn init(call_id: Option<Expression<F>>) -> Self {
        ConstraintBuilder {
            expressions: vec![],
            lookups: vec![],
            stack_offset: 0,
            call_id: call_id,
        }
    }

    // Common

    pub(crate) fn require_boolean(&mut self, value: Expression<F>) {
        self.add_expression(value.clone() * (1.expr() - value));
    }

    pub(crate) fn require_zero(&mut self, expression: Expression<F>) {
        self.add_expression(expression);
    }

    pub(crate) fn require_equal(
        &mut self,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) {
        self.add_expression((lhs) - (rhs));
    }

    pub(crate) fn require_in_range(
        &mut self,
        value: Expression<F>,
        range: u64,
    ) {
        let table = match range {
            32 => FixedLookup::Range32,
            256 => FixedLookup::Range256,
            _ => unimplemented!(),
        };
        self.add_lookup(Lookup::FixedLookup(
            table,
            [value, 0.expr(), 0.expr()],
        ));
    }

    pub(crate) fn require_in_set(
        &mut self,
        value: Expression<F>,
        set: Vec<Expression<F>>,
    ) {
        let mut expression = 1.expr();
        for set_value in set.iter() {
            expression = expression * (value.clone() - set_value.clone());
        }
        self.add_expression(expression);
    }

    // Stack

    pub(crate) fn stack_pop(&mut self, value: Expression<F>) {
        self.stack_lookup(value, false);
        self.stack_offset += 1;
    }

    pub(crate) fn stack_push(&mut self, value: Expression<F>) {
        self.stack_offset -= 1;
        self.stack_lookup(value, true);
    }

    fn stack_lookup(&mut self, value: Expression<F>, is_write: bool) {
        self.add_lookup(Lookup::BusMappingLookup(BusMappingLookup::Stack {
            index_offset: self.stack_offset,
            value: value,
            is_write: is_write,
        }));
    }

    // Memory

    pub(crate) fn memory_write(
        &mut self,
        address: Expression<F>,
        bytes: Vec<Expression<F>>,
    ) {
        self.memory_lookup(address, bytes, true)
    }

    pub(crate) fn memory_read(
        &mut self,
        address: Expression<F>,
        bytes: Vec<Expression<F>>,
    ) {
        self.memory_lookup(address, bytes, false);
    }

    fn memory_lookup(
        &mut self,
        address: Expression<F>,
        bytes: Vec<Expression<F>>,
        is_write: bool,
    ) {
        for idx in 0..bytes.len() {
            self.add_lookup(Lookup::BusMappingLookup(
                BusMappingLookup::Memory {
                    call_id: self.call_id.clone().unwrap(),
                    index: address.clone()
                        + Expression::Constant(F::from_u64(idx as u64)),
                    value: bytes[bytes.len() - 1 - idx].clone(),
                    is_write: is_write,
                },
            ));
        }
    }

    // General

    pub(crate) fn add_expression(&mut self, expression: Expression<F>) {
        self.expressions.push(expression);
    }

    pub(crate) fn add_expressions(&mut self, expressions: Vec<Expression<F>>) {
        self.expressions.extend(expressions);
    }

    pub(crate) fn add_lookup(&mut self, lookup: Lookup<F>) {
        self.lookups.push(lookup);
    }

    // Constraint

    pub(crate) fn constraint(
        &self,
        selector: Expression<F>,
        name: &'static str,
    ) -> Constraint<F> {
        Constraint {
            name: name,
            selector: selector,
            polys: self.expressions.clone(),
            lookups: self.lookups.clone(),
        }
    }
}
