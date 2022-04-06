use super::Opcode;
use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::operation::RW;
use crate::Error;
use eth_types::GethExecStep;

#[derive(Debug, Copy, Clone)]
pub(crate) struct ChainId;

impl Opcode for ChainId {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        // Get the chain_id from next step
        let chain_id = geth_steps[1].stack.last()?;

        // Stack write of the chain_id
        state.push_stack_op(
            &mut exec_step,
            RW::WRITE,
            geth_step.stack.last_filled().map(|a| a - 1),
            chain_id,
        )?;

        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod chainid_tests {
    use super::*;
    use crate::{circuit_input_builder::ExecState, mock::BlockData, operation::StackOp};
    use eth_types::{
        bytecode,
        evm_types::{OpcodeId, StackAddress},
        geth_types::GethData,
    };

    use mock::test_ctx::{helpers::*, TestContext};
    use mock::MOCK_CHAIN_ID;
    use pretty_assertions::assert_eq;

    #[test]
    fn chainid_opcode_impl() {
        let code = bytecode! {
            CHAINID
            STOP
        };

        // Geth the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |block, _tx| block,
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::CHAINID))
            .unwrap();

        assert_eq!(
            {
                let operation =
                    &builder.block.container.stack[step.bus_mapping_instance[0].as_usize()];
                (operation.rw(), operation.op())
            },
            (
                RW::WRITE,
                &StackOp::new(1, StackAddress::from(1023), *MOCK_CHAIN_ID)
            )
        );
    }
}
