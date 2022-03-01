use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_ACCOUNT_ADDRESS,
        step::ExecutionState,
        table::{CallContextFieldTag, TxContextFieldTag},
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            from_bytes, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::Field;
use eth_types::ToLittleEndian;
use halo2_proofs::{circuit::Region, plonk::Error};
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub(crate) struct OriginGadget<F> {
    same_context: SameContextGadget<F>,
    origin: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
}

impl<F: Field> ExecutionGadget<F> for OriginGadget<F> {
    const NAME: &'static str = "ORIGIN";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ORIGIN;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let origin = cb.query_rlc::<N_BYTES_ACCOUNT_ADDRESS>();
        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);

        // Lookup rw_table -> call_context with tx origin address
        cb.tx_context_lookup(
            tx_id.expr(),
            TxContextFieldTag::CallerAddress,
            None, // None because unrelated to calldata
            from_bytes::expr(&origin.cells),
        );

        // Push the value to the stack
        cb.stack_push(origin.expr());

        // State transition
        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(2.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition, None);

        Self {
            same_context,
            origin,
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
        println!("block {:?}", block);
        self.same_context.assign_exec_step(region, offset, step)?;
        println!("step.rw_indices[1] {:?}", step.rw_indices[1]);

        let origin = block.rws[step.rw_indices[1]].stack_value();

        self.origin.assign(
            region,
            offset,
            Some(
                origin.to_le_bytes()[..N_BYTES_ACCOUNT_ADDRESS]
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

    fn test_ok() {
        let bytecode = bytecode! {
            #[start]
            ORIGIN
            STOP
        };
        assert_eq!(run_test_circuits(bytecode), Ok(()));
    }
    #[test]
    fn origin_gadget_test() {
        test_ok();
    }
}
