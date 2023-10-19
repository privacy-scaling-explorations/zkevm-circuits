use std::marker::PhantomData;

use crate::{
    evm_circuit::{
        step::ExecutionState,
        util::{
            constraint_builder::{EVMConstraintBuilder, StepStateTransition},
            CachedRegion,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::plonk::Error;

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct EndChunkGadget<F> {
    _marker: PhantomData<F>,
}

impl<F: Field> ExecutionGadget<F> for EndChunkGadget<F> {
    const NAME: &'static str = "EndChunk";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndChunk;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        // State transition
        cb.not_step_last(|cb| {
            // Propagate  all the way down.
            cb.require_step_state_transition(StepStateTransition::same());
        });

        cb.step_last(|cb| {
            cb.step_state_lookup(1.expr());
        });

        cb.step_last_constraint_rwc();

        // TODO constraint Rw::Padding are append consecutively to avoid malicious insert

        Self {
            _marker: PhantomData {},
        }
    }

    fn assign_exec_step(
        &self,
        _region: &mut CachedRegion<'_, '_, F>,
        _offset: usize,
        _block: &Block<F>,
        _: &Transaction,
        _: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::bytecode;
    use mock::TestContext;

    fn test_ok(bytecode: bytecode::Bytecode) {
        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
        )
        .run()
    }

    #[test]
    fn end_chunk_test() {
        let bytecode = bytecode! {
            STOP
        };
        test_ok(bytecode);
    }
}
