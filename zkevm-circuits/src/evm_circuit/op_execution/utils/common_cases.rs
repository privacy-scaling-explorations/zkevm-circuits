use super::super::{
    Case, CaseAllocation, CaseConfig, Cell, Constraint, CoreStateInstance,
    ExecutionStep, OpExecutionState,
};
use super::constraint_builder::ConstraintBuilder;
use crate::util::Expr;
use halo2::plonk::Error;
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
        alloc: &CaseAllocation<F>,
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
            gas_used: gas_used,
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
        _state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        self.case_selector
            .assign(region, offset, Some(F::from_u64(0)))
            .unwrap();
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
        alloc: &CaseAllocation<F>,
        num_popped: usize,
    ) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            num_popped: num_popped,
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
        region: &mut Region<'_, F>,
        offset: usize,
        _state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        self.case_selector
            .assign(region, offset, Some(F::from_u64(0)))
            .unwrap();
        Ok(())
    }
}
