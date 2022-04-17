use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_DIFFICULTY,
        step::ExecutionState,
        table::BlockContextFieldTag,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            from_bytes, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::{circuit::Region, plonk::Error};
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub(crate) struct DifficultyGadget<F> {
    same_context: SameContextGadget<F>,
    difficulty: RandomLinearCombination<F, N_BYTES_DIFFICULTY>,
}

impl<F: Field> ExecutionGadget<F> for DifficultyGadget<F> {
    const NAME: &'static str = "DIFFICULTY";

    const EXECUTION_STATE: ExecutionState = ExecutionState::DIFFICULTY;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let difficulty = cb.query_rlc::<N_BYTES_DIFFICULTY>();
        cb.stack_push(difficulty.expr());

        // Lookup block table with difficulty
        cb.block_lookup(
            BlockContextFieldTag::Difficulty.expr(),
            None,
            from_bytes::expr(&difficulty.cells),
        );

        // State transition
        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::DIFFICULTY.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            difficulty,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let difficulty = block.rws[step.rw_indices[0]].stack_value();

        self.difficulty.assign(
            region,
            offset,
            Some(
                difficulty.to_le_bytes()[..N_BYTES_DIFFICULTY]
                    .try_into()
                    .unwrap(),
            ),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::bytecode;
    use mock::TestContext;

    #[test]
    fn difficulty_gadget_test() {
        let bytecode = bytecode! {
            DIFFICULTY
            STOP
        };

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }
}
