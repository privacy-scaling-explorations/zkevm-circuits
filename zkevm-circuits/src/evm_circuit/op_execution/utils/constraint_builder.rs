use super::super::super::{BusMappingLookup, Constraint, FixedLookup, Lookup};
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

// Default max degree allowed in all expressions passing through the
// ConstraintBuilder.
const DEFAULT_MAX_DEGREE: usize = 2usize.pow(4) + 1;
// Degree added for expressions used in lookups.
const LOOKUP_DEGREE: usize = 3;

#[derive(Clone, Debug)]
pub struct ConstraintBuilder<F> {
    pub expressions: Vec<Expression<F>>,
    pub(crate) lookups: Vec<Lookup<F>>,
    pub stack_offset: i32,
    pub gc_offset: usize,
    pub call_id: Option<Expression<F>>,
    pub max_degree: usize,
}

impl<F: FieldExt> ConstraintBuilder<F> {
    pub(crate) fn with_call_id(call_id: Expression<F>) -> Self {
        Self::init(DEFAULT_MAX_DEGREE, Some(call_id))
    }

    pub(crate) fn with_max_degree(mag_degree: usize) -> Self {
        Self::init(mag_degree, None)
    }

    pub(crate) fn default() -> Self {
        Self::init(DEFAULT_MAX_DEGREE, None)
    }

    fn init(max_degree: usize, call_id: Option<Expression<F>>) -> Self {
        ConstraintBuilder {
            expressions: vec![],
            lookups: vec![],
            stack_offset: 0,
            gc_offset: 0,
            call_id,
            max_degree,
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
            16 => FixedLookup::Range16,
            17 => FixedLookup::Range17,
            32 => FixedLookup::Range32,
            256 => FixedLookup::Range256,
            512 => FixedLookup::Range512,
            _ => unimplemented!(),
        };
        self.add_fixed_lookup(table, [value, 0.expr(), 0.expr()]);
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
        self.stack_lookup(self.stack_offset.expr(), value, false.expr());
        self.stack_offset += 1;
    }

    pub(crate) fn stack_push(&mut self, value: Expression<F>) {
        self.stack_offset -= 1;
        self.stack_lookup(self.stack_offset.expr(), value, true.expr());
    }

    pub(crate) fn stack_lookup(
        &mut self,
        index_offset: Expression<F>,
        value: Expression<F>,
        is_write: Expression<F>,
    ) {
        self.stack_lookup_at(
            index_offset,
            value,
            is_write,
            self.gc_offset.expr(),
        );
        self.gc_offset += 1;
    }

    pub(crate) fn stack_lookup_at(
        &mut self,
        index_offset: Expression<F>,
        value: Expression<F>,
        is_write: Expression<F>,
        gc_offset: Expression<F>,
    ) {
        self.validate_lookup_expression(&index_offset);
        self.validate_lookup_expression(&value);
        self.validate_lookup_expression(&is_write);
        self.validate_lookup_expression(&gc_offset);
        self.add_lookup(Lookup::BusMappingLookup(BusMappingLookup::Stack {
            index_offset,
            value,
            is_write,
            gc_offset,
        }));
    }

    // Memory

    pub(crate) fn memory_lookup(
        &mut self,
        address: Expression<F>,
        byte: Expression<F>,
        is_write: Expression<F>,
    ) {
        self.memory_lookup_at(address, byte, is_write, self.gc_offset.expr());
        self.gc_offset += 1;
    }

    pub(crate) fn memory_lookup_at(
        &mut self,
        address: Expression<F>,
        byte: Expression<F>,
        is_write: Expression<F>,
        gc_offset: Expression<F>,
    ) {
        self.validate_lookup_expression(&self.call_id.clone().unwrap());
        self.validate_lookup_expression(&address);
        self.validate_lookup_expression(&byte);
        self.validate_lookup_expression(&is_write);
        self.validate_lookup_expression(&gc_offset);
        self.add_lookup(Lookup::BusMappingLookup(BusMappingLookup::Memory {
            call_id: self.call_id.clone().unwrap(),
            index: address,
            value: byte,
            is_write,
            gc_offset,
        }));
    }

    // Validation

    pub(crate) fn validate_expression(&self, expression: &Expression<F>) {
        self.validate_degree(expression.degree());
    }

    pub(crate) fn validate_lookup_expression(
        &self,
        expression: &Expression<F>,
    ) {
        self.validate_degree(expression.degree() + LOOKUP_DEGREE);
    }

    pub(crate) fn validate_degree(&self, degree: usize) {
        assert!(
            degree <= self.max_degree,
            "Expression degree too high: {} > {}",
            degree,
            self.max_degree,
        );
    }

    // General

    pub(crate) fn add_expression(&mut self, expression: Expression<F>) {
        self.validate_expression(&expression);
        self.expressions.push(expression);
    }

    pub(crate) fn add_expressions(&mut self, expressions: Vec<Expression<F>>) {
        for expression in expressions {
            self.add_expression(expression);
        }
    }

    pub(crate) fn add_fixed_lookup(
        &mut self,
        table: FixedLookup,
        expressions: [Expression<F>; 3],
    ) {
        for expression in expressions.iter() {
            self.validate_lookup_expression(expression);
        }
        self.add_lookup(Lookup::FixedLookup(table, expressions));
    }

    pub(crate) fn add_bytecode_lookup(
        &mut self,
        expressions: [Expression<F>; 4],
    ) {
        for expression in expressions.iter() {
            self.validate_lookup_expression(expression);
        }
        self.add_lookup(Lookup::BytecodeLookup(expressions));
    }

    fn add_lookup(&mut self, lookup: Lookup<F>) {
        self.lookups.push(lookup);
    }

    // Constraint

    pub(crate) fn constraint(
        &self,
        selector: Expression<F>,
        name: &'static str,
    ) -> Constraint<F> {
        Constraint {
            name,
            selector,
            polys: self.expressions.clone(),
            lookups: self.lookups.clone(),
        }
    }
}
