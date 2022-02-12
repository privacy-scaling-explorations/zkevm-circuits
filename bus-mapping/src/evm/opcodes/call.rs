use super::Opcode;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    operation::{
        AccountField, AccountOp, CallContextField, CallContextOp, StackOp, TxAccessListAccountOp,
        RW,
    },
    Error,
};
use eth_types::{
    evm_types::{eip150_gas, memory_expansion_gas_cost, GasCost},
    GethExecStep, ToWord,
};

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the `OpcodeId::DUP*` `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Call;

impl Opcode for Call {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let tx_id = state.tx_ctx.id();
        let call = state.call()?.clone();
        let callee = state.parse_call(geth_step)?;

        for (field, value) in [
            (CallContextField::TxId, tx_id.into()),
            (CallContextField::RwCounterEndOfReversion, 0.into()),
            (
                CallContextField::IsPersistent,
                (call.is_persistent as u64).into(),
            ),
            (CallContextField::CallerAddress, call.address.to_word()),
            (CallContextField::IsStatic, (call.is_static as u64).into()),
            (CallContextField::Depth, call.depth.into()),
        ] {
            state.push_op(
                &mut exec_step,
                RW::READ,
                CallContextOp {
                    call_id: call.call_id,
                    field,
                    value,
                },
            );
        }

        for i in 0..7 {
            state.push_op(
                &mut exec_step,
                RW::READ,
                StackOp {
                    call_id: call.call_id,
                    address: geth_step.stack.nth_last_filled(i),
                    value: geth_step.stack.nth_last(i)?,
                },
            );
        }
        state.push_op(
            &mut exec_step,
            RW::WRITE,
            StackOp {
                call_id: call.call_id,
                address: geth_step.stack.nth_last_filled(6),
                value: (callee.is_success as u64).into(),
            },
        );

        let is_warm_access = !state.sdb.add_account_to_access_list(callee.address);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id,
                address: callee.address,
                value: true,
                value_prev: is_warm_access,
            },
        )?;

        // Switch to callee's call context
        state.push_call(callee.clone());

        for (field, value) in [
            (CallContextField::RwCounterEndOfReversion, 0.into()),
            (
                CallContextField::IsPersistent,
                (callee.is_persistent as u64).into(),
            ),
        ] {
            state.push_op(
                &mut exec_step,
                RW::READ,
                CallContextOp {
                    call_id: callee.call_id,
                    field,
                    value,
                },
            );
        }

        let (found, caller_account) = state.sdb.get_account_mut(&callee.caller_address);
        if !found {
            return Err(Error::AccountNotFound(callee.caller_address));
        }
        let caller_balance_prev = caller_account.balance;
        let caller_balance = caller_account.balance - callee.value;
        caller_account.balance = caller_balance;
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            AccountOp {
                address: callee.caller_address,
                field: AccountField::Balance,
                value: caller_balance,
                value_prev: caller_balance_prev,
            },
        )?;

        let (found, callee_account) = state.sdb.get_account_mut(&callee.address);
        if !found {
            return Err(Error::AccountNotFound(callee.address));
        }
        let is_account_empty = callee_account.is_empty();
        let callee_balance_prev = callee_account.balance;
        let callee_balance = callee_account.balance + callee.value;
        callee_account.balance = callee_balance;
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            AccountOp {
                address: callee.address,
                field: AccountField::Balance,
                value: callee_balance,
                value_prev: callee_balance_prev,
            },
        )?;

        let (_, account) = state.sdb.get_account_mut(&callee.address);
        for (field, value) in [
            (AccountField::Nonce, account.nonce),
            (AccountField::CodeHash, account.code_hash.to_word()),
        ] {
            state.push_op(
                &mut exec_step,
                RW::READ,
                AccountOp {
                    address: callee.address,
                    field,
                    value,
                    value_prev: value,
                },
            );
        }

        // Calculate next_memory_word_size and callee_gas_left manually in case
        // there isn't next geth_step (e.g. callee doesn't have code).
        let next_memory_word_size = [
            geth_step.memory.word_size() as u64,
            (callee.call_data_offset + callee.call_data_length + 31) / 32,
            (callee.return_data_offset + callee.return_data_length + 31) / 32,
        ]
        .into_iter()
        .max()
        .unwrap();
        let has_value = !callee.value.is_zero();
        let gas_cost = if is_warm_access {
            GasCost::WARM_ACCESS.0
        } else {
            GasCost::COLD_ACCOUNT_ACCESS.0
        } + if is_account_empty {
            GasCost::CALL_EMPTY_ACCOUNT.0
        } else {
            0
        } + if has_value {
            GasCost::CALL_WITH_VALUE.0
        } else {
            0
        } + memory_expansion_gas_cost(
            geth_step.memory.word_size() as u64,
            next_memory_word_size,
        );
        let callee_gas_left = eip150_gas(geth_step.gas.0 - gas_cost, geth_step.stack.last()?);

        for (field, value) in [
            (CallContextField::IsRoot, (call.is_root as u64).into()),
            (CallContextField::IsCreate, (call.is_create() as u64).into()),
            (CallContextField::CodeSource, call.code_hash.to_word()),
            (
                CallContextField::ProgramCounter,
                (geth_step.pc.0 + 1).into(),
            ),
            (
                CallContextField::StackPointer,
                (geth_step.stack.stack_pointer().0 + 6).into(),
            ),
            (
                CallContextField::GasLeft,
                (geth_step.gas.0 - gas_cost - callee_gas_left).into(),
            ),
            (CallContextField::MemorySize, next_memory_word_size.into()),
            (
                CallContextField::StateWriteCounter,
                (exec_step.swc + 1).into(),
            ),
        ] {
            state.push_op(
                &mut exec_step,
                RW::WRITE,
                CallContextOp {
                    call_id: call.call_id,
                    field,
                    value,
                },
            );
        }

        for (field, value) in [
            (CallContextField::CallerId, call.call_id.into()),
            (CallContextField::TxId, tx_id.into()),
            (CallContextField::Depth, callee.depth.into()),
            (
                CallContextField::CallerAddress,
                callee.caller_address.to_word(),
            ),
            (CallContextField::CalleeAddress, callee.address.to_word()),
            (
                CallContextField::CallDataOffset,
                callee.call_data_offset.into(),
            ),
            (
                CallContextField::CallDataLength,
                callee.call_data_length.into(),
            ),
            (
                CallContextField::ReturnDataOffset,
                callee.return_data_offset.into(),
            ),
            (
                CallContextField::ReturnDataLength,
                callee.return_data_length.into(),
            ),
            (CallContextField::Value, callee.value),
            (
                CallContextField::IsSuccess,
                (callee.is_success as u64).into(),
            ),
            (CallContextField::IsStatic, (callee.is_static as u64).into()),
            (CallContextField::LastCalleeId, 0.into()),
            (CallContextField::LastCalleeReturnDataOffset, 0.into()),
            (CallContextField::LastCalleeReturnDataLength, 0.into()),
        ] {
            state.push_op(
                &mut exec_step,
                RW::READ,
                CallContextOp {
                    call_id: callee.call_id,
                    field,
                    value,
                },
            );
        }

        Ok(vec![exec_step])
    }
}
