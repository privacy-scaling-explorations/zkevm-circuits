use std::marker::PhantomData;

use crate::{
    evm_circuit::{
        step::ExecutionState,
        util::{
            constraint_builder::{EVMConstraintBuilder, StepStateTransition, Transition::Delta},
            CachedRegion,
        },
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::plonk::Error;

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct BeginChunkGadget<F> {
    _marker: PhantomData<F>,
}

impl<F: Field> ExecutionGadget<F> for BeginChunkGadget<F> {
    const NAME: &'static str = "BeginChunk";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BeginChunk;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        // state lookup
        cb.step_state_lookup(0.expr());
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(cb.rw_counter_offset()),
            ..StepStateTransition::same()
        };
        cb.require_step_state_transition(step_state_transition);
        Self {
            _marker: PhantomData {},
        }
    }

    fn assign_exec_step(
        &self,
        _region: &mut CachedRegion<'_, '_, F>,
        _offset: usize,
        _block: &Block<F>,
        _chunk: &Chunk<F>,
        _: &Transaction,
        _: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[cfg(test)]
mod test {
    // begin_chunk unittest covered by end_chunk
}
