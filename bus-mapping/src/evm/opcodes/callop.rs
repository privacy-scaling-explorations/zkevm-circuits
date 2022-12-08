use super::Opcode;
use crate::circuit_input_builder::{CallKind, CircuitInputStateRef, CodeSource, ExecStep};
use crate::operation::{AccountField, CallContextField, TxAccessListAccountOp, RW};
use crate::Error;
use eth_types::evm_types::gas_utils::{eip150_gas, memory_expansion_gas_cost};
use eth_types::evm_types::GasCost;
use eth_types::{GethExecStep, ToWord};
use keccak256::EMPTY_HASH;
use log::warn;

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the `OpcodeId::CALL`, `OpcodeId::CALLCODE`,
/// `OpcodeId::DELEGATECALL` and `OpcodeId::STATICCALL`.
/// - CALL and CALLCODE: N_ARGS = 7
/// - DELEGATECALL and STATICCALL: N_ARGS = 6
#[derive(Debug, Copy, Clone)]
pub(crate) struct CallOpcode<const N_ARGS: usize>;

impl<const N_ARGS: usize> Opcode for CallOpcode<N_ARGS> {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let args_offset = geth_step.stack.nth_last(N_ARGS - 4)?.as_usize();
        let args_length = geth_step.stack.nth_last(N_ARGS - 3)?.as_usize();
        let ret_offset = geth_step.stack.nth_last(N_ARGS - 2)?.as_usize();
        let ret_length = geth_step.stack.nth_last(N_ARGS - 1)?.as_usize();

        // we need to keep the memory until parse_call complete
        state.call_expand_memory(args_offset, args_length, ret_offset, ret_length)?;

        let tx_id = state.tx_ctx.id();
        let call = state.parse_call(geth_step)?;
        let current_call = state.call()?.clone();

        // For both CALLCODE and DELEGATECALL opcodes, `call.address` is caller
        // address which is different from callee_address (code address).
        let callee_address = match call.code_source {
            CodeSource::Address(address) => address,
            _ => call.address,
        };

        let mut field_values = vec![
            (CallContextField::TxId, tx_id.into()),
            // NOTE: For `RwCounterEndOfReversion` we use the `0` value as a
            // placeholder, and later set the proper value in
            // `CircuitInputBuilder::set_value_ops_call_context_rwc_eor`
            (CallContextField::RwCounterEndOfReversion, 0.into()),
            (
                CallContextField::IsPersistent,
                (current_call.is_persistent as u64).into(),
            ),
            (
                CallContextField::IsStatic,
                (current_call.is_static as u64).into(),
            ),
            (CallContextField::Depth, current_call.depth.into()),
            (
                CallContextField::CalleeAddress,
                current_call.address.to_word(),
            ),
        ];
        if call.kind == CallKind::DelegateCall {
            field_values.extend([
                (
                    CallContextField::CallerAddress,
                    current_call.caller_address.to_word(),
                ),
                (CallContextField::Value, current_call.value),
            ]);
        }
        for (field, value) in field_values {
            state.call_context_read(&mut exec_step, current_call.call_id, field, value);
        }

        for i in 0..N_ARGS {
            state.stack_read(
                &mut exec_step,
                geth_step.stack.nth_last_filled(i),
                geth_step.stack.nth_last(i)?,
            )?;
        }

        state.stack_write(
            &mut exec_step,
            geth_step.stack.nth_last_filled(N_ARGS - 1),
            (call.is_success as u64).into(),
        )?;

        let is_warm = state.sdb.check_account_in_access_list(&callee_address);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id,
                address: callee_address,
                is_warm: true,
                is_warm_prev: is_warm,
            },
        )?;

        // Switch to callee's call context
        state.push_call(call.clone());

        for (field, value) in [
            (CallContextField::RwCounterEndOfReversion, 0.into()),
            (
                CallContextField::IsPersistent,
                (call.is_persistent as u64).into(),
            ),
        ] {
            state.call_context_write(&mut exec_step, call.call_id, field, value);
        }

        let (_, callee_account) = state.sdb.get_account(&call.address);
        let is_empty_account = callee_account.is_empty();
        let callee_nonce = callee_account.nonce;

        if call.kind == CallKind::Call {
            state.transfer(
                &mut exec_step,
                call.caller_address,
                call.address,
                call.value,
            )?;
        } else {
            let callee_balance = callee_account.balance;
            state.account_read(
                &mut exec_step,
                call.address,
                AccountField::Balance,
                callee_balance,
                callee_balance,
            )?;
        }

        state.account_read(
            &mut exec_step,
            call.address,
            AccountField::Nonce,
            callee_nonce,
            callee_nonce,
        )?;
        let callee_code_hash = call.code_hash;
        let callee_code_hash_word = callee_code_hash.to_word();
        state.account_read(
            &mut exec_step,
            callee_address,
            AccountField::CodeHash,
            callee_code_hash_word,
            callee_code_hash_word,
        )?;

        // Calculate next_memory_word_size and callee_gas_left manually in case
        // there isn't next geth_step (e.g. callee doesn't have code).
        debug_assert_eq!(exec_step.memory_size % 32, 0);
        let curr_memory_word_size = (exec_step.memory_size as u64) / 32;
        let next_memory_word_size = [
            curr_memory_word_size,
            (call.call_data_offset + call.call_data_length + 31) / 32,
            (call.return_data_offset + call.return_data_length + 31) / 32,
        ]
        .into_iter()
        .max()
        .unwrap();

        let has_value = !call.value.is_zero();
        let memory_expansion_gas_cost =
            memory_expansion_gas_cost(curr_memory_word_size, next_memory_word_size);
        let gas_cost = if is_warm {
            GasCost::WARM_ACCESS.as_u64()
        } else {
            GasCost::COLD_ACCOUNT_ACCESS.as_u64()
        } + if has_value {
            GasCost::CALL_WITH_VALUE.as_u64()
                + if is_empty_account {
                    GasCost::NEW_ACCOUNT.as_u64()
                } else {
                    0
                }
        } else {
            0
        } + memory_expansion_gas_cost;
        let gas_specified = geth_step.stack.last()?;
        let callee_gas_left = eip150_gas(geth_step.gas.0 - gas_cost, gas_specified);

        // There are 3 branches from here.
        match (
            state.is_precompiled(&call.address),
            callee_code_hash.to_fixed_bytes() == *EMPTY_HASH,
        ) {
            // 1. Call to precompiled.
            (true, _) => {
                warn!("Call to precompiled is left unimplemented");
                Ok(vec![exec_step])
            }
            // 2. Call to account with empty code.
            (_, true) => {
                for (field, value) in [
                    (CallContextField::LastCalleeId, 0.into()),
                    (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                    (CallContextField::LastCalleeReturnDataLength, 0.into()),
                ] {
                    state.call_context_write(&mut exec_step, current_call.call_id, field, value);
                }
                state.handle_return(geth_step)?;
                Ok(vec![exec_step])
            }
            // 3. Call to account with non-empty code.
            (_, false) => {
                for (field, value) in [
                    (
                        CallContextField::ProgramCounter,
                        (geth_step.pc.0 + 1).into(),
                    ),
                    (
                        CallContextField::StackPointer,
                        (geth_step.stack.stack_pointer().0 + N_ARGS - 1).into(),
                    ),
                    (
                        CallContextField::GasLeft,
                        (geth_step.gas.0 - gas_cost - callee_gas_left).into(),
                    ),
                    (CallContextField::MemorySize, next_memory_word_size.into()),
                    (
                        CallContextField::ReversibleWriteCounter,
                        (exec_step.reversible_write_counter + 1).into(),
                    ),
                ] {
                    state.call_context_write(&mut exec_step, current_call.call_id, field, value);
                }

                for (field, value) in [
                    (CallContextField::CallerId, current_call.call_id.into()),
                    (CallContextField::TxId, tx_id.into()),
                    (CallContextField::Depth, call.depth.into()),
                    (
                        CallContextField::CallerAddress,
                        call.caller_address.to_word(),
                    ),
                    (CallContextField::CalleeAddress, call.address.to_word()),
                    (
                        CallContextField::CallDataOffset,
                        call.call_data_offset.into(),
                    ),
                    (
                        CallContextField::CallDataLength,
                        call.call_data_length.into(),
                    ),
                    (
                        CallContextField::ReturnDataOffset,
                        call.return_data_offset.into(),
                    ),
                    (
                        CallContextField::ReturnDataLength,
                        call.return_data_length.into(),
                    ),
                    (CallContextField::Value, call.value),
                    (CallContextField::IsSuccess, (call.is_success as u64).into()),
                    (CallContextField::IsStatic, (call.is_static as u64).into()),
                    (CallContextField::LastCalleeId, 0.into()),
                    (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                    (CallContextField::LastCalleeReturnDataLength, 0.into()),
                    (CallContextField::IsRoot, 0.into()),
                    (CallContextField::IsCreate, 0.into()),
                    (CallContextField::CodeHash, call.code_hash.to_word()),
                ] {
                    state.call_context_write(&mut exec_step, call.call_id, field, value);
                }

                Ok(vec![exec_step])
            }
        }
    }
}
