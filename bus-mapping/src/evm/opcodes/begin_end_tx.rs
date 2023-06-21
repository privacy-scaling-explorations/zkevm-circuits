use super::TxExecSteps;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecState, ExecStep},
    operation::{AccountField, AccountOp, CallContextField, TxReceiptField, TxRefundOp, RW},
    state_db::CodeDB,
    Error,
};
use eth_types::{
    evm_types::{GasCost, MAX_REFUND_QUOTIENT_OF_GAS_USED},
    evm_unimplemented, ToWord, Word,
};
use ethers_core::utils::get_contract_address;

#[derive(Clone, Copy, Debug)]
pub(crate) struct BeginEndTx;

impl TxExecSteps for BeginEndTx {
    fn gen_associated_steps(
        state: &mut CircuitInputStateRef,
        execution_step: ExecState,
    ) -> Result<ExecStep, Error> {
        match execution_step {
            ExecState::BeginTx => gen_begin_tx_steps(state),
            ExecState::EndTx => gen_end_tx_steps(state),
            _ => {
                unreachable!()
            }
        }
    }
}

fn gen_begin_tx_steps(state: &mut CircuitInputStateRef) -> Result<ExecStep, Error> {
    let mut exec_step = state.new_begin_tx_step();
    let call = state.call()?.clone();

    for (field, value) in [
        (CallContextField::TxId, state.tx_ctx.id().into()),
        (
            CallContextField::RwCounterEndOfReversion,
            call.rw_counter_end_of_reversion.into(),
        ),
        (
            CallContextField::IsPersistent,
            (call.is_persistent as usize).into(),
        ),
        (CallContextField::IsSuccess, call.is_success.to_word()),
    ] {
        state.call_context_write(&mut exec_step, call.call_id, field, value);
    }

    // Increase caller's nonce when the tx is not invalid
    let caller_address = call.caller_address;
    let nonce_prev = state.sdb.get_account(&caller_address).1.nonce;
    let nonce = if !state.tx.invalid_tx {
        nonce_prev + 1
    } else {
        nonce_prev
    };
    state.account_write(
        &mut exec_step,
        caller_address,
        AccountField::Nonce,
        nonce.into(),
        nonce_prev.into(),
    )?;

    // Add caller and callee into access list
    for address in [call.caller_address, call.address] {
        let is_warm_prev = !state.sdb.add_account_to_access_list(address);
        state.tx_accesslist_account_write(
            &mut exec_step,
            state.tx_ctx.id(),
            address,
            true,
            is_warm_prev,
        )?;
    }

    let intrinsic_gas_cost = if state.tx.is_create() {
        GasCost::CREATION_TX.as_u64()
    } else {
        GasCost::TX.as_u64()
    } + state.tx.tx.call_data_gas_cost();

    // Don't pay any fee or transfer any ETH for invalid transactions
    let (gas_cost, value, fee) = if state.tx.invalid_tx {
        (0, Word::zero(), Some(Word::zero()))
    } else {
        (
            intrinsic_gas_cost,
            call.value,
            Some(state.tx.tx.gas_price * state.tx.gas()),
        )
    };

    // Set the gas cost
    exec_step.gas_cost = GasCost(gas_cost);

    // Get code_hash of callee
    let (_, callee_account) = state.sdb.get_account(&call.address);
    let callee_exists = !callee_account.is_empty();
    let (callee_code_hash, is_empty_code_hash) = if callee_exists {
        (
            call.code_hash.to_word(),
            call.code_hash == CodeDB::empty_code_hash(),
        )
    } else {
        (Word::zero(), true)
    };
    if !state.is_precompiled(&call.address) && !call.is_create() {
        state.account_read(
            &mut exec_step,
            call.address,
            AccountField::CodeHash,
            callee_code_hash,
        );
    }

    // Transfer with fee
    state.transfer_with_fee(
        &mut exec_step,
        call.caller_address,
        call.address,
        callee_exists,
        call.is_create(),
        value,
        fee,
    )?;

    // In case of contract creation we wish to verify the correctness of the
    // contract's address (callee). This address is defined as:
    //
    // Keccak256(RLP([tx_caller, tx_nonce]))[12:]
    //
    // We feed the RLP-encoded bytes to the block's SHA3 inputs, which gets assigned
    // to the Keccak circuit, so that the BeginTxGadget can do a lookup to the
    // Keccak table and verify the contract address.
    if state.tx.is_create() {
        state.block.sha3_inputs.push({
            let mut stream = ethers_core::utils::rlp::RlpStream::new();
            stream.begin_list(2);
            stream.append(&caller_address);
            stream.append(&nonce_prev);
            stream.out().to_vec()
        });
    }

    // There are 4 branches from here.
    match (
        call.is_create(),
        state.is_precompiled(&call.address),
        is_empty_code_hash || state.tx.invalid_tx,
    ) {
        // 1. Creation transaction.
        (true, _, _) => {
            state.push_op_reversible(
                &mut exec_step,
                AccountOp {
                    address: call.address,
                    field: AccountField::Nonce,
                    value: 1.into(),
                    value_prev: 0.into(),
                },
            )?;
            for (field, value) in [
                (CallContextField::Depth, call.depth.into()),
                (
                    CallContextField::CallerAddress,
                    call.caller_address.to_word(),
                ),
                (
                    CallContextField::CalleeAddress,
                    get_contract_address(caller_address, nonce_prev).to_word(),
                ),
                (
                    CallContextField::CallDataOffset,
                    call.call_data_offset.into(),
                ),
                (
                    CallContextField::CallDataLength,
                    state.tx.tx.call_data.len().into(),
                ),
                (CallContextField::Value, call.value),
                (CallContextField::IsStatic, (call.is_static as usize).into()),
                (CallContextField::LastCalleeId, 0.into()),
                (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                (CallContextField::LastCalleeReturnDataLength, 0.into()),
                (CallContextField::IsRoot, 1.into()),
                (CallContextField::IsCreate, 1.into()),
                (CallContextField::CodeHash, call.code_hash.to_word()),
            ] {
                state.call_context_write(&mut exec_step, call.call_id, field, value);
            }
            Ok(exec_step)
        }
        // 2. Call to precompiled.
        (_, true, _) => {
            evm_unimplemented!("Call to precompiled is left unimplemented");
            Ok(exec_step)
        }
        (_, _, do_not_run_code) => {
            // 3. Call to account with empty code.
            if do_not_run_code {
                return Ok(exec_step);
            }

            // 4. Call to account with non-empty code/invalid tx.
            for (field, value) in [
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
                (CallContextField::Value, call.value),
                (CallContextField::IsStatic, (call.is_static as usize).into()),
                (CallContextField::LastCalleeId, 0.into()),
                (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                (CallContextField::LastCalleeReturnDataLength, 0.into()),
                (CallContextField::IsRoot, 1.into()),
                (CallContextField::IsCreate, 0.into()),
                (CallContextField::CodeHash, callee_code_hash),
            ] {
                state.call_context_write(&mut exec_step, call.call_id, field, value);
            }

            Ok(exec_step)
        }
    }
}

fn gen_end_tx_steps(state: &mut CircuitInputStateRef) -> Result<ExecStep, Error> {
    let mut exec_step = state.new_end_tx_step();
    let call = state.tx.calls()[0].clone();

    state.call_context_read(
        &mut exec_step,
        call.call_id,
        CallContextField::TxId,
        state.tx_ctx.id().into(),
    );
    state.call_context_read(
        &mut exec_step,
        call.call_id,
        CallContextField::IsPersistent,
        Word::from(call.is_persistent as u8),
    );

    let refund = state.sdb.refund();
    state.push_op(
        &mut exec_step,
        RW::READ,
        TxRefundOp {
            tx_id: state.tx_ctx.id(),
            value: refund,
            value_prev: refund,
        },
    );

    let effective_refund = refund
        .min((state.tx.gas() - exec_step.gas_left.0) / MAX_REFUND_QUOTIENT_OF_GAS_USED as u64);
    let (found, caller_account) = state.sdb.get_account(&call.caller_address);
    if !found {
        return Err(Error::AccountNotFound(call.caller_address));
    }
    let caller_balance_prev = caller_account.balance;
    let caller_balance =
        caller_balance_prev + state.tx.tx.gas_price * (exec_step.gas_left.0 + effective_refund);
    state.account_write(
        &mut exec_step,
        call.caller_address,
        AccountField::Balance,
        caller_balance,
        caller_balance_prev,
    )?;

    let effective_tip = state.tx.tx.gas_price - state.block.base_fee;
    let (found, coinbase_account) = state.sdb.get_account(&state.block.coinbase);
    if !found {
        return Err(Error::AccountNotFound(state.block.coinbase));
    }
    let coinbase_balance_prev = coinbase_account.balance;
    let coinbase_balance =
        coinbase_balance_prev + effective_tip * (state.tx.gas() - exec_step.gas_left.0);
    state.account_write(
        &mut exec_step,
        state.block.coinbase,
        AccountField::Balance,
        coinbase_balance,
        coinbase_balance_prev,
    )?;

    // handle tx receipt tag
    state.tx_receipt_write(
        &mut exec_step,
        state.tx_ctx.id(),
        TxReceiptField::PostStateOrStatus,
        call.is_persistent as u64,
    )?;

    let log_id = exec_step.log_id;
    state.tx_receipt_write(
        &mut exec_step,
        state.tx_ctx.id(),
        TxReceiptField::LogLength,
        log_id as u64,
    )?;

    if state.tx_ctx.id() > 1 {
        // query pre tx cumulative gas
        state.tx_receipt_read(
            &mut exec_step,
            state.tx_ctx.id() - 1,
            TxReceiptField::CumulativeGasUsed,
            state.block_ctx.cumulative_gas_used,
        )?;
    }

    state.block_ctx.cumulative_gas_used += state.tx.gas() - exec_step.gas_left.0;
    state.tx_receipt_write(
        &mut exec_step,
        state.tx_ctx.id(),
        TxReceiptField::CumulativeGasUsed,
        state.block_ctx.cumulative_gas_used,
    )?;

    if !state.tx_ctx.is_last_tx() {
        state.call_context_write(
            &mut exec_step,
            state.block_ctx.rwc.0 + 1,
            CallContextField::TxId,
            (state.tx_ctx.id() + 1).into(),
        );
    }

    Ok(exec_step)
}
