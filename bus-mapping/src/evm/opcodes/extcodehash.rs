use super::Opcode;
use crate::circuit_input_builder::CircuitInputStateRef;
use crate::operation::{
    AccountField, AccountOp, CallContextField, CallContextOp, TxAccessListAccountOp, RW,
};
use crate::Error;
use eth_types::{GethExecStep, ToAddress, ToWord, evm_types::GasCost};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Extcodehash;

impl Opcode for Extcodehash {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];

        let stack_address = step.stack.last_filled();

        let external_address = step.stack.last()?.to_address();
        let code_hash = steps[1].stack.last()?;

        state.push_stack_op(RW::READ, stack_address, external_address.to_word());

        state.push_op(
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().into(),
            },
        );

        let account_previously_accessed = match step.gas_cost {
            GasCost::WARM_STORAGE_READ_COST => true,
            GasCost::COLD_ACCOUNT_ACCESS_COST => false,
            _ => unreachable!(),
        };

        state.push_op(
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id: state.tx_ctx.id(),
                address: external_address,
                value: true,
                value_prev: account_previously_accessed,
            },
        );

        // Account read for code hash of external account
        state.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::CodeHash,
                value: code_hash,
                value_prev: code_hash,
            },
        );

        // Stack write of the the code
        state.push_stack_op(RW::WRITE, stack_address.map(|a| a - 1), code_hash);

        Ok(())
    }
}

#[cfg(test)]
mod extcodehash_tests {
    use super::*;
    use crate::{
        circuit_input_builder::{ExecStep, TransactionContext},
        mock::BlockData,
    };
    use eth_types::{address, bytecode, evm_types::StackAddress, ToWord};
    use eth_types::{H160, U256};
    use mock::new_single_tx_trace_code_at_start;
    use pretty_assertions::assert_eq;

    #[test]
    fn nonexistent_account() -> Result<(), Error> {
        // Test the case where the account doesn't exist, because there is not
        // any code deployed at address 0xaabbccddee000000000000000000000000000000.
        test_ok(
            address!("0xaabbccddee000000000000000000000000000000"),
            false,
        )
    }

    #[test]
    fn existing_account() -> Result<(), Error> {
        // new_single_tx_trace_code_at_start works by executing code deployed at the
        // default address so in this test case the account will exist, meaning that the
        // external code hash returned will not be 0.
        test_ok(H160::default(), true)
    }

    fn test_ok(address: H160, account_should_exist: bool) -> Result<(), Error> {
        let code = bytecode! {
            PUSH20(address.to_word())
            #[start]
            EXTCODEHASH
            STOP
        };

        // Get the execution steps from the external tracer
        let block = BlockData::new_from_geth_data(new_single_tx_trace_code_at_start(&code)?);

        let mut builder = block.new_circuit_input_builder();
        builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

        let mut test_builder = block.new_circuit_input_builder();
        let mut tx = test_builder
            .new_tx(&block.eth_tx, !block.geth_trace.failed)
            .unwrap();
        let mut tx_ctx = TransactionContext::new(&block.eth_tx, &block.geth_trace).unwrap();

        // Generate step corresponding to CALLER
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            0,
            test_builder.block_ctx.rwc,
            0,
        );
        let gas_cost = step.gas_cost;
        let mut state_ref = test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        // Add the Stack pop
        state_ref.push_stack_op(RW::READ, StackAddress::from(1023), address.to_word());

        state_ref.push_op(
            RW::READ,
            CallContextOp {
                call_id: state_ref.call().call_id,
                field: CallContextField::TxId,
                value: state_ref.tx_ctx.id().into(),
            },
        );

        let account_previously_accessed = match gas_cost {
            GasCost::WARM_STORAGE_READ_COST => true,
            GasCost::COLD_ACCOUNT_ACCESS_COST => false,
            _ => unreachable!(),
        };
        state_ref.push_op(
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id: state_ref.tx_ctx.id(),
                address,
                value: true,
                value_prev: account_previously_accessed,
            },
        );

        let (account_exists, account) = state_ref.sdb.get_account(&address);
        assert_eq!(account_should_exist, account_exists);

        let code_hash = if account_exists {
            account.code_hash.to_word()
        } else {
            U256::zero()
        };

        // Add the code hash read
        state_ref.push_op(
            RW::READ,
            AccountOp {
                address,
                field: AccountField::CodeHash,
                value: code_hash,
                value_prev: code_hash,
            },
        );

        // Add the Stack write
        state_ref.push_stack_op(RW::WRITE, StackAddress::from(1022), code_hash);

        tx.steps_mut().push(step);
        test_builder.block.txs_mut().push(tx);

        // Compare first step bus mapping instance
        assert_eq!(
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
            test_builder.block.txs()[0].steps()[0].bus_mapping_instance,
        );

        // Compare containers
        assert_eq!(builder.block.container, test_builder.block.container);

        Ok(())
    }
}
