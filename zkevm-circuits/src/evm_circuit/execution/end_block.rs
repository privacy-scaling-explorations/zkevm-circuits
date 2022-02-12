use crate::evm_circuit::{
    execution::ExecutionGadget,
    step::ExecutionState,
    util::constraint_builder::ConstraintBuilder,
    witness::{Block, Call, ExecStep, Transaction},
};
use eth_types::Field;
use halo2_proofs::{circuit::Region, plonk::Error};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(crate) struct EndBlockGadget<F> {
    _marker: PhantomData<F>,
}

impl<F: Field> ExecutionGadget<F> for EndBlockGadget<F> {
    const NAME: &'static str = "EndBlock";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndBlock;

    fn configure(_: &mut ConstraintBuilder<F>) -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    fn assign_exec_step(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _: &Block<F>,
        _: &Transaction,
        _: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}
