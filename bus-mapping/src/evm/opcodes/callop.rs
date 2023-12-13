use super::Opcode;
use crate::{
    circuit_input_builder::{
        CallKind, CircuitInputStateRef, CodeSource, CopyDataType, CopyEvent, ExecStep, NumberOrHash,
    },
    evm::opcodes::{
        error_oog_precompile::ErrorOOGPrecompile,
        precompiles::gen_associated_ops as precompile_associated_ops,
    },
    operation::{AccountField, CallContextField, TxAccessListAccountOp},
    precompile::{execute_precompiled, is_precompiled, PrecompileCalls},
    state_db::CodeDB,
    Error,
};
use eth_types::{
    evm_types::{
        gas_utils::{eip150_gas, memory_expansion_gas_cost},
        GasCost, OpcodeId, GAS_STIPEND_CALL_WITH_VALUE,
    },
    GethExecStep, ToWord, Word,
};
use std::cmp::min;

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

        // In offset and length are truncated to Uint64 for call opcodes as:
        // <https://github.com/ethereum/go-ethereum/blob/84c3799e21d61d677965715fe09f8209660b4009/core/vm/instructions.go#L672>
        let args_offset = geth_step.stack.nth_last(N_ARGS - 4)?.low_u64() as usize;
        let args_length = geth_step.stack.nth_last(N_ARGS - 3)?.as_usize();
        let ret_offset = geth_step.stack.nth_last(N_ARGS - 2)?.low_u64() as usize;
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
            state.call_context_read(&mut exec_step, current_call.call_id, field, value)?;
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

        let callee_code_hash = call.code_hash;
        let callee = state.sdb.get_account(&callee_address).1.clone();
        let callee_exists = !callee.is_empty();

        let (callee_code_hash_word, is_empty_code_hash) = if callee_exists {
            (
                callee_code_hash.to_word(),
                callee_code_hash == CodeDB::empty_code_hash(),
            )
        } else {
            (Word::zero(), true)
        };
        state.account_read(
            &mut exec_step,
            callee_address,
            AccountField::CodeHash,
            callee_code_hash_word,
        )?;

        let is_warm = state.sdb.check_account_in_access_list(&callee_address);
        state.push_op_reversible(
            &mut exec_step,
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
            state.call_context_write(&mut exec_step, call.clone().call_id, field, value)?;
        }

        let (found, sender_account) = state.sdb.get_account(&call.caller_address);
        debug_assert!(found);

        let caller_balance = sender_account.balance;

        let is_call_or_callcode = call.kind == CallKind::Call || call.kind == CallKind::CallCode;
        let is_sufficient = caller_balance >= call.value;
        let is_valid_depth = geth_step.depth < 1025;

        // Precheck is OK when depth is in range and caller balance is sufficient
        let is_precheck_ok = is_valid_depth && (is_sufficient || !is_call_or_callcode);

        log::debug!(
            "is_precheck_ok: {}, call type: {:?}, sender_account: {:?} ",
            is_precheck_ok,
            call.kind,
            call.caller_address
        );

        // read balance of caller to compare to value for insufficient_balance checking
        // in circuit, also use for callcode successful case check balance is
        // indeed larger than transfer value. for call opcode, it does in
        // tranfer gadget implicitly.
        state.account_read(
            &mut exec_step,
            call.caller_address,
            AccountField::Balance,
            caller_balance,
        )?;

        let code_address = call.code_address();
        let is_precompile = code_address
            .map(|ref addr| is_precompiled(addr))
            .unwrap_or(false);
        // CALLCODE does not need to do real transfer
        // Transfer value only when all these conditions met:
        // - The opcode is CALL
        // - The precheck passed
        // - The value to send is not zero
        if call.kind == CallKind::Call && is_precheck_ok && !call.value.is_zero() {
            state.transfer(
                &mut exec_step,
                call.caller_address,
                call.address,
                callee_exists,
                false,
                call.value,
            )?;
        }

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

        let has_value = !call.value.is_zero() && !call.is_delegatecall();
        let memory_expansion_gas_cost =
            memory_expansion_gas_cost(curr_memory_word_size, next_memory_word_size);

        let gas_cost = if is_warm {
            GasCost::WARM_ACCESS
        } else {
            GasCost::COLD_ACCOUNT_ACCESS
        } + if has_value {
            GasCost::CALL_WITH_VALUE
                + if call.kind == CallKind::Call && !callee_exists {
                    GasCost::NEW_ACCOUNT
                } else {
                    0
                }
        } else {
            0
        } + memory_expansion_gas_cost;
        let gas_specified = geth_step.stack.last()?;

        let stipend = if has_value {
            GAS_STIPEND_CALL_WITH_VALUE
        } else {
            0
        };
        let callee_gas_left = eip150_gas(geth_step.gas - gas_cost, gas_specified);
        let callee_gas_left_with_stipend = callee_gas_left + stipend;

        // There are 4 branches from here.
        // add failure case for insufficient balance or error depth in the future.
        if geth_steps[0].op == OpcodeId::CALL
            && geth_steps[1].depth == geth_steps[0].depth + 1
            && geth_steps[1].gas != callee_gas_left_with_stipend
        {
            // panic with full info
            let info1 = format!("callee_gas_left {callee_gas_left} gas_specified {gas_specified} gas_cost {gas_cost} is_warm {is_warm} has_value {has_value} current_memory_word_size {curr_memory_word_size} next_memory_word_size {next_memory_word_size}, memory_expansion_gas_cost {memory_expansion_gas_cost}");
            let info2 = format!("args gas:{:?} addr:{:?} value:{:?} cd_pos:{:?} cd_len:{:?} rd_pos:{:?} rd_len:{:?}",
                        geth_step.stack.nth_last(0),
                        geth_step.stack.nth_last(1),
                        geth_step.stack.nth_last(2),
                        geth_step.stack.nth_last(3),
                        geth_step.stack.nth_last(4),
                        geth_step.stack.nth_last(5),
                        geth_step.stack.nth_last(6)
                    );
            let full_ctx = format!(
                "step0 {:?} step1 {:?} call {:?}, {} {}",
                geth_steps[0], geth_steps[1], call, info1, info2
            );
            debug_assert_eq!(
                geth_steps[1].gas, callee_gas_left_with_stipend,
                "{full_ctx}"
            );
        }

        match (is_precheck_ok, is_precompile, is_empty_code_hash) {
            // 1. Call to precompiled.
            (true, true, _) => {
                let code_address = code_address.unwrap();
                let precompile_call: PrecompileCalls = code_address.0[19].into();

                // get the result of the precompile call.
                // For failed call, it will cost all gas provided
                let (result, precompile_call_gas_cost, has_oog_err) = execute_precompiled(
                    &code_address,
                    if args_length != 0 {
                        let caller_memory = &state.caller_ctx()?.memory;
                        &caller_memory.0[args_offset..args_offset + args_length]
                    } else {
                        &[]
                    },
                    callee_gas_left_with_stipend,
                );

                // mutate the callee memory by at least the precompile call's result that will be
                // written from memory addr 0 to memory addr result.len()
                state.call_ctx_mut()?.memory.extend_at_least(result.len());

                state.caller_ctx_mut()?.return_data = result.clone();

                let length = min(result.len(), ret_length);

                if length > 0 {
                    state
                        .caller_ctx_mut()?
                        .memory
                        .extend_at_least(ret_offset + length);
                }

                for (field, value) in [
                    (
                        CallContextField::IsSuccess,
                        Word::from(call.is_success as u64),
                    ),
                    (
                        CallContextField::CalleeAddress,
                        call.code_address().unwrap().to_word(),
                    ),
                    (CallContextField::CallerId, call.caller_id.into()),
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
                ] {
                    state.call_context_write(&mut exec_step, call.call_id, field, value)?;
                }

                let caller_ctx = state.caller_ctx_mut()?;
                caller_ctx.memory.0[ret_offset..ret_offset + length]
                    .copy_from_slice(&result[..length]);

                // return while restoring some of caller's context.
                for (field, value) in [
                    (CallContextField::ProgramCounter, (geth_step.pc + 1).into()),
                    (
                        CallContextField::StackPointer,
                        (geth_step.stack.stack_pointer().0 + N_ARGS - 1).into(),
                    ),
                    (
                        CallContextField::GasLeft,
                        (geth_step.gas - gas_cost - callee_gas_left).into(),
                    ),
                    (CallContextField::MemorySize, next_memory_word_size.into()),
                    (
                        CallContextField::ReversibleWriteCounter,
                        (exec_step.reversible_write_counter + 1).into(),
                    ),
                    (CallContextField::LastCalleeId, call.call_id.into()),
                    (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                    (
                        CallContextField::LastCalleeReturnDataLength,
                        result.len().into(),
                    ),
                ] {
                    state.call_context_write(&mut exec_step, current_call.call_id, field, value)?;
                }

                // insert a copy event (input) for this step and generate memory op
                let rw_counter_start = state.block_ctx.rwc;
                if call.call_data_length > 0 {
                    let n_input_bytes = if let Some(input_len) = precompile_call.input_len() {
                        min(input_len, call.call_data_length as usize)
                    } else {
                        call.call_data_length as usize
                    };

                    let input_bytes = state.gen_copy_steps_for_precompile_calldata(
                        &mut exec_step,
                        call.call_data_offset,
                        n_input_bytes as u64,
                    )?;

                    state.push_copy(
                        &mut exec_step,
                        CopyEvent {
                            src_id: NumberOrHash::Number(call.caller_id),
                            src_type: CopyDataType::Memory,
                            src_addr: call.call_data_offset,
                            src_addr_end: call.call_data_offset + n_input_bytes as u64,
                            dst_id: NumberOrHash::Number(call.call_id),
                            dst_type: CopyDataType::RlcAcc,
                            dst_addr: 0,
                            log_id: None,
                            rw_counter_start,
                            bytes: input_bytes.iter().map(|s| (*s, false)).collect(),
                        },
                    );
                }

                // write the result in the callee's memory
                let rw_counter_start = state.block_ctx.rwc;
                if call.is_success && !result.is_empty() {
                    let (output_bytes, _prev_bytes) = state
                        .gen_copy_steps_for_precompile_callee_memory(&mut exec_step, &result)?;

                    state.push_copy(
                        &mut exec_step,
                        CopyEvent {
                            src_id: NumberOrHash::Number(call.call_id),
                            src_type: CopyDataType::RlcAcc,
                            src_addr: 0,
                            src_addr_end: output_bytes.len() as u64,
                            dst_id: NumberOrHash::Number(call.call_id),
                            dst_type: CopyDataType::Memory,
                            dst_addr: 0,
                            log_id: None,
                            rw_counter_start,
                            bytes: output_bytes.iter().map(|s| (*s, false)).collect(),
                        },
                    );
                }

                // insert another copy event (output) for this step.
                let rw_counter_start = state.block_ctx.rwc;
                if call.is_success && length > 0 {
                    let return_bytes = state.gen_copy_steps_for_precompile_returndata(
                        &mut exec_step,
                        call.return_data_offset,
                        length,
                        &result,
                    )?;
                    state.push_copy(
                        &mut exec_step,
                        CopyEvent {
                            src_id: NumberOrHash::Number(call.call_id),
                            src_type: CopyDataType::Memory,
                            src_addr: 0,
                            src_addr_end: length as u64,
                            dst_id: NumberOrHash::Number(call.caller_id),
                            dst_type: CopyDataType::Memory,
                            dst_addr: call.return_data_offset,
                            log_id: None,
                            rw_counter_start,
                            bytes: return_bytes.iter().map(|s| (*s, false)).collect(),
                        },
                    );
                }

                if has_oog_err {
                    let mut oog_step = ErrorOOGPrecompile::gen_associated_ops(
                        state,
                        &geth_steps[1],
                        call.clone(),
                    )?;
                    oog_step.gas_left = callee_gas_left_with_stipend;
                    oog_step.gas_cost = precompile_call_gas_cost;
                    // Make the Precompile execution step to handle return logic and restore to
                    // caller context (similar as STOP and RETURN).
                    state.handle_return(&mut [&mut exec_step, &mut oog_step], geth_steps, true)?;

                    Ok(vec![exec_step, oog_step])
                } else {
                    let precompile_call: PrecompileCalls = code_address.0[19].into();

                    let mut precompile_step = precompile_associated_ops(
                        state,
                        geth_steps[1].clone(),
                        call.clone(),
                        precompile_call,
                    )?;

                    // Set gas left and gas cost for precompile step.
                    precompile_step.gas_left = callee_gas_left_with_stipend;
                    precompile_step.gas_cost = precompile_call_gas_cost;
                    // Make the Precompile execution step to handle return logic and restore to
                    // caller context (similar as STOP and RETURN).
                    state.handle_return(
                        &mut [&mut exec_step, &mut precompile_step],
                        geth_steps,
                        true,
                    )?;

                    debug_assert_eq!(
                        geth_steps[0].gas - gas_cost - precompile_call_gas_cost + stipend,
                        geth_steps[1].gas,
                        "precompile_call_gas_cost wrong {:?}",
                        precompile_step.exec_state
                    );

                    Ok(vec![exec_step, precompile_step])
                }
            }
            // 2. Call to account with empty code.
            (true, _, true) => {
                for (field, value) in [
                    (CallContextField::LastCalleeId, call.call_id.into()),
                    (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                    (CallContextField::LastCalleeReturnDataLength, 0.into()),
                ] {
                    state.call_context_write(&mut exec_step, current_call.call_id, field, value)?;
                }
                state.caller_ctx_mut()?.return_data.clear();
                state.handle_return(&mut [&mut exec_step], geth_steps, false)?;
                Ok(vec![exec_step])
            }
            // 3. Call to account with non-empty code.
            (true, _, false) => {
                for (field, value) in [
                    (CallContextField::ProgramCounter, (geth_step.pc + 1).into()),
                    (
                        CallContextField::StackPointer,
                        (geth_step.stack.stack_pointer().0 + N_ARGS - 1).into(),
                    ),
                    (
                        CallContextField::GasLeft,
                        (geth_step.gas - gas_cost - callee_gas_left).into(),
                    ),
                    (CallContextField::MemorySize, next_memory_word_size.into()),
                    (
                        CallContextField::ReversibleWriteCounter,
                        (exec_step.reversible_write_counter + 1).into(),
                    ),
                ] {
                    state.call_context_write(&mut exec_step, current_call.call_id, field, value)?;
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
                    state.call_context_write(&mut exec_step, call.call_id, field, value)?;
                }

                Ok(vec![exec_step])
            }
            // 4. insufficient balance or error depth cases.
            (false, _, _) => {
                for (field, value) in [
                    (CallContextField::LastCalleeId, call.call_id.into()),
                    (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                    (CallContextField::LastCalleeReturnDataLength, 0.into()),
                ] {
                    state.call_context_write(&mut exec_step, current_call.call_id, field, value)?;
                }
                state.caller_ctx_mut()?.return_data.clear();
                state.handle_return(&mut [&mut exec_step], geth_steps, false)?;
                Ok(vec![exec_step])
            }
        }
    }
}
