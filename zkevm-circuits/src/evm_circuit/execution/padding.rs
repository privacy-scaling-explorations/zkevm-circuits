use std::marker::PhantomData;

use crate::evm_circuit::{
    execution::ExecutionGadget,
    step::ExecutionState,
    util::{
        constraint_builder::{EVMConstraintBuilder, StepStateTransition},
        CachedRegion,
    },
    witness::{Block, Call, ExecStep, Transaction},
};
use eth_types::Field;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct PaddingGadget<F> {
    _phantom: PhantomData<F>,
}

impl<F: Field> ExecutionGadget<F> for PaddingGadget<F> {
    const NAME: &'static str = "Padding";

    const EXECUTION_STATE: ExecutionState = ExecutionState::Padding;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        cb.require_step_state_transition(StepStateTransition {
            ..StepStateTransition::same()
        });

        Self {
            _phantom: PhantomData,
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

    fn test_circuit(evm_circuit_pad_to: usize) {
        let bytecode = bytecode! {
            PUSH1(0)
            STOP
        };

        let ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap();

        // finish required tests using this witness block
        CircuitTestBuilder::<2, 1>::new_from_test_ctx(ctx)
            .block_modifier(Box::new(move |block| {
                block.circuits_params.max_evm_rows = evm_circuit_pad_to
            }))
            .run();
    }

    // Test where the EVM circuit has a fixed size and contains several Padding
    // at the end after the trace steps
    #[test]
    fn padding() {
        test_circuit(50);
    }
}
