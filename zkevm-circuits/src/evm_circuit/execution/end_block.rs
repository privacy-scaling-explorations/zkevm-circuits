use crate::evm_circuit::{
    execution::ExecutionGadget,
    step::ExecutionState,
    util::{constraint_builder::ConstraintBuilder, CachedRegion},
    witness::{Block, Call, ExecStep, Transaction},
};
use eth_types::Field;
use gadgets::not;
use halo2_proofs::plonk::Error;

use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(crate) struct EndBlockGadget<F, const MAX_TXS: usize> {
    _marker: PhantomData<F>,
}

impl<F: Field, const MAX_TXS: usize> ExecutionGadget<F> for EndBlockGadget<F, MAX_TXS> {
    const NAME: &'static str = "EndBlock";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndBlock;

    fn configure(_: &mut ConstraintBuilder<F>) -> Self {
        let is_last_step = cb.curr.state.;
        
        cb.condition(is_last_step.expr(), |cb| {});
        cb.condition(not::expr(is_last_step.expr()), |cb| {});

        Self {
            _marker: PhantomData,
        }
    }

    fn assign_exec_step(
        &self,
        _region: &mut CachedRegion<'_, '_, F>,
        _offset: usize,
        _: &Block<F>,
        _: &Transaction,
        _: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}
