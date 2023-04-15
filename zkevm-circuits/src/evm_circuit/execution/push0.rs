use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::BlockContextFieldTag,
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::{
    plonk::{
        Error,
        Expression::Constant,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct Push0Gadget<F> {
    same_context: SameContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for Push0Gadget<F> {
    const NAME: &'static str = "PUSH0";

    const EXECUTION_STATE: ExecutionState = ExecutionState::PUSH0;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // Push the value to the stack
        cb.stack_push(Constant(F::from(0u64)));

        // State transition
        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::PUSH0.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        _: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::bytecode;
    use mock::test_ctx::TestContext;

    #[test]
    fn push0_gadget_test() {
        let bytecode = bytecode! {
            #[start]
            PUSH0
            STOP
        };

        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
        )
        .run();
    }
}
