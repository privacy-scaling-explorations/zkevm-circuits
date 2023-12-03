use std::marker::PhantomData;

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{constraint_builder::EVMConstraintBuilder, CachedRegion},
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    util::word::{WordCell, WordExpr},
};
use eth_types::Field;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct DummyGadget<F, const N_POP: usize, const N_PUSH: usize, const S: ExecutionState> {
    pops: [WordCell<F>; N_POP],
    pushes: [WordCell<F>; N_PUSH],
    _marker: PhantomData<F>,
}

impl<F: Field, const N_POP: usize, const N_PUSH: usize, const S: ExecutionState> ExecutionGadget<F>
    for DummyGadget<F, N_POP, N_PUSH, S>
{
    const NAME: &'static str = "DUMMY";

    const EXECUTION_STATE: ExecutionState = S;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let pops: [WordCell<F>; N_POP] = [(); N_POP].map(|_| cb.query_word_unchecked());
        let pushes: [WordCell<F>; N_PUSH] = [(); N_PUSH].map(|_| cb.query_word_unchecked());
        for pop in pops.iter() {
            cb.stack_pop(pop.to_word());
        }
        for push in pushes.iter() {
            cb.stack_push(push.to_word());
        }
        Self {
            pops,
            pushes,
            _marker: PhantomData,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        chunk: &Chunk<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        // this happens if some opcodes are in the
        // process of being implemented but are still
        // using DummyGadget.
        // See `bus-mapping/src/evm/opcodes.rs`
        if step.rw_indices_len() != N_POP + N_PUSH {
            log::warn!("DummyGadget: wrong number of rw indices for {:?}", step);
        }

        for i in 0..N_POP {
            let value = block.get_rws(step, i).stack_value();
            self.pops[i].assign_u256(region, offset, value)?;
        }
        for i in 0..N_PUSH {
            let value = block.get_rws(step, N_POP + i).stack_value();
            self.pushes[i].assign_u256(region, offset, value)?;
        }
        Ok(())
    }
}
