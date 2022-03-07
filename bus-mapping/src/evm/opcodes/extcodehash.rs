use super::Opcode;
use crate::{
    circuit_input_builder::CircuitInputStateRef,
    operation::{
        AccountField, AccountOp, CallContextField, CallContextOp, TxAccessListAccountOp, RW,
    },
    state_db::Account,
    Error,
};
use eth_types::{evm_types::GasCost, GethExecStep, ToAddress, ToWord};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Extcodehash;

impl Opcode for Extcodehash {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        let stack_address = step.stack.last_filled();

        // Pop external address off stack
        let external_address = step.stack.last()?.to_address();
        state.push_stack_op(RW::READ, stack_address, external_address.to_word());

        // Read transaction id from call context
        state.push_op(
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().into(),
            },
        );

        // Update transaction access list for external_address
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

        // These three lookups are required to determine the existence of the external
        // account
        let &Account {
            nonce,
            code_hash,
            balance,
            ..
        } = state.sdb.get_account(&external_address).1;
        state.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::Nonce,
                value: nonce,
                value_prev: nonce,
            },
        );
        state.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::Balance,
                value: balance,
                value_prev: balance,
            },
        );
        state.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::CodeHash,
                value: code_hash.to_word(),
                value_prev: code_hash.to_word(),
            },
        );

        // Stack write of the result of EXTCODEHASH.
        state.push_stack_op(RW::WRITE, stack_address, steps[1].stack.last()?);

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
    use eth_types::{
        address, bytecode, evm_types::StackAddress, geth_types::Account as GethAccount, Address,
        Bytecode, Bytes, U256,
    };
    use mock::new_single_tx_trace_accounts;
    use pretty_assertions::assert_eq;

    #[test]
    fn cold_empty_account() -> Result<(), Error> {
        test_ok(false, false)
    }

    #[test]
    fn warm_empty_account() -> Result<(), Error> {
        test_ok(false, true)
    }

    #[test]
    fn cold_existing_account() -> Result<(), Error> {
        test_ok(true, false)
    }

    #[test]
    fn warm_existing_account() -> Result<(), Error> {
        test_ok(true, true)
    }

    fn test_ok(exists: bool, is_warm: bool) -> Result<(), Error> {
        // In each test case, this is the external address we will call EXTCODEHASH on.
        let external_address = address!("0xaabbccddee000000000000000000000000000000");

        // Make the external account warm, if needed, by first getting its balance.
        let mut code = Bytecode::default();
        if is_warm {
            code.append(&bytecode! {
                PUSH20(external_address.to_word())
                BALANCE
                POP
            });
        }
        code.append(&bytecode! {
            PUSH20(external_address.to_word())
            #[start]
            EXTCODEHASH
            STOP
        });

        let mut accounts = vec![GethAccount {
            address: Address::default(), // This is the address of the executing account
            code: Bytes::from(code.to_vec()),
            ..Default::default()
        }];
        // Let the external account exist, if needed, by making its code non-empty
        if exists {
            accounts.push(GethAccount {
                address: external_address,
                code: Bytes::from([34, 54, 56]),
                ..Default::default()
            })
        }

        // Get the execution steps from the external tracer
        let mut geth_data = new_single_tx_trace_accounts(accounts)?;
        geth_data.geth_trace.struct_logs =
            geth_data.geth_trace.struct_logs[code.get_pos("start")..].to_vec();
        let block = BlockData::new_from_geth_data(geth_data);

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

        // Sanity check that address is actually warm if that is what we're testing.
        assert_eq!(is_warm, step.gas_cost == GasCost::WARM_STORAGE_READ_COST);

        let mut state_ref = test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        // Add the Stack pop
        state_ref.push_stack_op(
            RW::READ,
            StackAddress::from(1023),
            external_address.to_word(),
        );

        state_ref.push_op(
            RW::READ,
            CallContextOp {
                call_id: state_ref.call().call_id,
                field: CallContextField::TxId,
                value: state_ref.tx_ctx.id().into(),
            },
        );

        state_ref.push_op(
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id: state_ref.tx_ctx.id(),
                address: external_address,
                value: true,
                value_prev: is_warm,
            },
        );

        let (
            account_exists,
            &Account {
                nonce,
                balance,
                code_hash,
                ..
            },
        ) = state_ref.sdb.get_account(&external_address);
        assert_eq!(exists, account_exists);

        // Add the nonce, balance, code hash reads
        state_ref.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::Nonce,
                value: nonce,
                value_prev: nonce,
            },
        );
        state_ref.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::Balance,
                value: balance,
                value_prev: balance,
            },
        );
        state_ref.push_op(
            RW::READ,
            AccountOp {
                address: external_address,
                field: AccountField::CodeHash,
                value: code_hash.to_word(),
                value_prev: code_hash.to_word(),
            },
        );

        // Add the stack write
        state_ref.push_stack_op(
            RW::WRITE,
            StackAddress::from(1023),
            if account_exists {
                code_hash.to_word()
            } else {
                U256::zero()
            },
        );

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
