use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    error::ExecError,
    evm::Opcode,
    Error,
};
use eth_types::GethExecStep;

#[derive(Debug, Copy, Clone)]
pub struct ErrorCodeStore;

/// handle CodeStoreOutOfGas and MaxCodeSizeExceeded two errors
impl Opcode for ErrorCodeStore {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = geth_steps.get(1);

        exec_step.error = state.get_step_err(geth_step, next_step)?;

        assert!(
            exec_step.error == Some(ExecError::CodeStoreOutOfGas)
                || exec_step.error == Some(ExecError::MaxCodeSizeExceeded)
        );

        let offset = geth_step.stack.nth_last(0)?;
        let length = geth_step.stack.nth_last(1)?;
        state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(0), offset)?;
        state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(1), length)?;

        // in internal call context
        let call = state.call()?;

        // create context check
        assert!(call.is_create());

        state.handle_return(&mut exec_step, geth_steps, true)?;
        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{circuit_input_builder::ExecState, mock::BlockData, operation::RW};
    use eth_types::{bytecode, evm_types::OpcodeId, geth_types::GethData};
    use mock::{
        test_ctx::helpers::{account_0_code_account_1_no_code, tx_from_1_to_0},
        TestContext,
    };

    #[test]
    fn test_max_code_size_exceed() {
        // code_creator outputs an empty array of length 0x6000 + 1, which will
        // trigger the max code size limit.
        let code_len = 0x6000 + 1;
        let code_creator = bytecode! {
            .op_mstore(code_len, 0x00)
            .op_return(0x00, code_len)
        };
        let mut code = bytecode! {};
        code.store_code_to_mem(&code_creator);

        code.append(&bytecode! {
            PUSH1 (code_creator.codesize())
            PUSH1 (0x0)
            PUSH1 (0)
            CREATE

            PUSH1 (0x20)
            PUSH1 (0x20)
            PUSH1 (0x20)
            PUSH1 (0)
            PUSH1 (0)
            DUP6
            PUSH2 (0xFFFF)
            CALL
            STOP
        });

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        let builder = builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let tx_id = 1;
        let transaction = &builder.block.txs()[tx_id - 1];
        let step = transaction
            .steps()
            .iter()
            .filter(|step| step.exec_state == ExecState::Op(OpcodeId::RETURN))
            .last()
            .unwrap();

        assert_eq!(step.error, Some(ExecError::MaxCodeSizeExceeded));

        let container = builder.block.container.clone();
        let operation = &container.stack[step.bus_mapping_instance[0].as_usize()];
        assert_eq!(operation.rw(), RW::READ);
    }
}
