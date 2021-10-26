use super::super::{
    Case, CaseAllocation, CaseConfig, Cell, Constraint, CoreStateInstance,
    ExecutionStep, OpExecutionState,
};
use super::constraint_builder::ConstraintBuilder;
use crate::util::Expr;
use halo2::plonk::{Error, Expression};
use halo2::{arithmetic::FieldExt, circuit::Region};

pub const STACK_START_IDX: usize = 1024;

#[derive(Clone, Debug)]
pub(crate) struct OutOfGasCase<F> {
    case_selector: Cell<F>,
    gas_available: Cell<F>,
    gas_used: usize,
}

impl<F: FieldExt> OutOfGasCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::OutOfGas,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(crate) fn construct(
        alloc: &mut CaseAllocation<F>,
        gas_used: usize,
    ) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            gas_available: alloc
                .resumption
                .as_ref()
                .unwrap()
                .gas_available
                .clone(),
            gas_used,
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let gas_overdemand = state_curr.gas_counter.expr()
            + self.gas_used.expr()
            - self.gas_available.expr();
        let set = (1..=self.gas_used).map(|i| i.expr()).collect();
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(gas_overdemand, set);
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        self.gas_available.assign(
            region,
            offset,
            Some(F::from_u64(state.gas_counter as u64)),
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct StackUnderflowCase<F> {
    case_selector: Cell<F>,
    num_popped: usize,
}

impl<F: FieldExt> StackUnderflowCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::StackUnderflow,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(crate) fn construct(
        alloc: &mut CaseAllocation<F>,
        num_popped: usize,
    ) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            num_popped,
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let set = (0..self.num_popped)
            .map(|i| (STACK_START_IDX - i).expr())
            .collect();
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(state_curr.stack_pointer.expr(), set);
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RangeStackUnderflowCase<F> {
    case_selector: Cell<F>,
    start_op: u64,
    range: u64,
}

impl<F: FieldExt> RangeStackUnderflowCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::StackUnderflow,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(crate) fn construct(
        alloc: &mut CaseAllocation<F>,
        start_op: u64,
        range: u64,
    ) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            start_op,
            range,
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::default();

        // The stack index we have to peek, deduced from the opcode and `start_op`
        let stack_offset = state_curr.opcode.expr() - self.start_op.expr();

        // Stack underflow when
        //  `STACK_START_IDX <= state_curr.stack_pointer.expr() + stack_offset < STACK_START_IDX + range`
        cb.require_in_range(
            state_curr.stack_pointer.expr() + stack_offset
                - STACK_START_IDX.expr(),
            self.range,
        );

        // Generate the constraint
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct StackOverflowCase<F> {
    case_selector: Cell<F>,
    num_pushed: usize,
}

impl<F: FieldExt> StackOverflowCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::StackOverflow,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(crate) fn construct(
        alloc: &mut CaseAllocation<F>,
        num_pushed: usize,
    ) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            num_pushed,
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let set = (0..self.num_pushed).map(|i| i.expr()).collect();
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(state_curr.stack_pointer.expr(), set);
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

pub(crate) fn require_opcode_in_set<F: FieldExt>(
    value: Expression<F>,
    set: Vec<Expression<F>>,
) -> ConstraintBuilder<F> {
    let mut cb = ConstraintBuilder::default();
    cb.require_in_set(value, set);
    cb
}

pub(crate) fn require_opcode_in_range<F: FieldExt>(
    value: Expression<F>,
    set: Vec<Expression<F>>,
) -> ConstraintBuilder<F> {
    assert!(!set.is_empty());
    let mut cb = ConstraintBuilder::default();
    cb.require_in_range(value - set[0].clone(), set.len() as u64);
    cb
}
