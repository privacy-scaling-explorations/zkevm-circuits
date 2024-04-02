use super::Opcode;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    operation::{CallContextField, StorageOp, TxAccessListAccountStorageOp, RW},
    Error,
};
use eth_types::{GethExecStep, ToWord, Word};

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the [`OpcodeId::TLOAD`](crate::evm::OpcodeId::TLOAD)
/// `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Tload;

impl Opcode for Tload {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let call_id = state.call()?.call_id;
        let contract_addr = state.call()?.address;

        state.call_context_read(
            &mut exec_step,
            call_id,
            CallContextField::TxId,
            Word::from(state.tx_ctx.id()),
        )?;

        state.call_context_read(
            &mut exec_step,
            call_id,
            CallContextField::RwCounterEndOfReversion,
            Word::from(state.call()?.rw_counter_end_of_reversion),
        )?;

        state.call_context_read(
            &mut exec_step,
            call_id,
            CallContextField::IsPersistent,
            Word::from(state.call()?.is_persistent as u8),
        )?;

        state.call_context_read(
            &mut exec_step,
            call_id,
            CallContextField::CalleeAddress,
            contract_addr.to_word(),
        )?;

        // First stack read
        let key = geth_step.stack.last()?;
        let stack_position = geth_step.stack.last_filled();

        // Manage first stack read at latest stack position
        state.stack_read(&mut exec_step, stack_position, key)?;

        // Storage read
        let value = geth_step.storage.get_or_err(&key)?;

        let is_warm = state
            .sdb
            .check_account_storage_in_access_list(&(contract_addr, key));

        let (_, committed_value) = state.sdb.get_committed_storage(&contract_addr, &key);
        let committed_value = *committed_value;
        state.push_op(
            &mut exec_step,
            RW::READ,
            StorageOp::new(
                contract_addr,
                key,
                value,
                value,
                state.tx_ctx.id(),
                committed_value,
            ),
        )?;

        // First stack write
        state.stack_write(&mut exec_step, stack_position, value)?;
        state.push_op(
            &mut exec_step,
            RW::READ,
            TxAccessListAccountStorageOp {
                tx_id: state.tx_ctx.id(),
                address: contract_addr,
                key,
                is_warm,
                is_warm_prev: is_warm,
            },
        )?;
        state.push_op_reversible(
            &mut exec_step,
            TxAccessListAccountStorageOp {
                tx_id: state.tx_ctx.id(),
                address: contract_addr,
                key,
                is_warm: true,
                is_warm_prev: is_warm,
            },
        )?;

        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod tload_tests {
    use super::*;
    use crate::{
        circuit_input_builder::ExecState,
        mock::BlockData,
        operation::{StackOp, TransientStorageOp},
    };
    use eth_types::{
        bytecode,
        evm_types::{OpcodeId, StackAddress},
        geth_types::GethData,
        Word,
    };
    use mock::{
        test_ctx::{helpers::*, TestContext},
        MOCK_ACCOUNTS,
    };
    use pretty_assertions::assert_eq;

    fn test_ok() {
        let code = bytecode! {
            // Load transient storage slot 0
            PUSH1(0x00u64)
            TLOAD
            STOP
        };
        let expected_loaded_value = 0;

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

        println!("{:#?}", builder.block.txs()[0].steps());
        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::TLOAD))
            .unwrap();

        assert_eq!(
            [4, 6]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|operation| (operation.rw(), operation.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1023), Word::from(0x0u32))
                ),
                (
                    RW::WRITE,
                    &StackOp::new(1, StackAddress::from(1023), Word::from(expected_loaded_value))
                )
            ]
        );

        let transient_storage_op =
            &builder.block.container.transient_storage[step.bus_mapping_instance[5].as_usize()];
        assert_eq!(
            (transient_storage_op.rw(), transient_storage_op.op()),
            (
                RW::READ,
                &TransientStorageOp::new(
                    MOCK_ACCOUNTS[0],
                    Word::from(0x0u32),
                    Word::from(expected_loaded_value),
                    Word::from(expected_loaded_value),
                    1,
                )
            )
        );
    }

    #[test]
    fn tload_opcode_impl_warm() {
        test_ok()
    }
}
