use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        table::BlockContextFieldTag,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            Cell, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::ToLittleEndian;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct TimestampGadget<F> {
    same_context: SameContextGadget<F>,
    timestamp: Cell<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for TimestampGadget<F> {
    const NAME: &'static str = "TIMESTAMP";

    const EXECUTION_STATE: ExecutionState = ExecutionState::TIMESTAMP;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let timestamp = cb.query_cell();
        cb.stack_push(timestamp.expr());

        // Lookup block table with timestamp
        cb.block_lookup(
            BlockContextFieldTag::Timestamp.expr(),
            None,
            timestamp.expr(),
        );

        // State transition
        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition, None);

        Self {
            same_context,
            timestamp,
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

        self.timestamp.assign(
            region,
            offset,
            Some(RandomLinearCombination::random_linear_combine(
                block.context.timestamp.to_le_bytes(),
                block.randomness,
            )),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::bytecode;

    fn test_ok() {
        let bytecode = bytecode! {
            #[start]
            TIMESTAMP
            STOP
        };
        assert_eq!(run_test_circuits(bytecode), Ok(()));
    }
    #[test]
    fn timestamp_gadget_test() {
        test_ok();
    }
}
