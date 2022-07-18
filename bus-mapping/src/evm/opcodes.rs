//! Definition of each opcode of the EVM.
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    evm::OpcodeId,
    operation::{
        AccountField, CallContextField, TxAccessListAccountOp, TxReceiptField, TxRefundOp, RW,
    },
    Error,
};
use core::fmt::Debug;
use eth_types::{
    evm_types::{GasCost, MAX_REFUND_QUOTIENT_OF_GAS_USED},
    GethExecStep, ToAddress, ToWord, Word,
};
use keccak256::EMPTY_HASH;
use log::warn;
use std::collections::HashMap;

mod call;
mod calldatacopy;
mod calldataload;
mod calldatasize;
mod caller;
mod callvalue;
mod chainid;
mod codecopy;
mod codesize;
mod create;
mod dup;
mod extcodecopy;
mod extcodehash;
mod gasprice;
mod logs;
mod mload;
mod mstore;
mod number;
mod origin;
mod r#return;
mod returndatacopy;
mod selfbalance;
mod sha3;
mod sload;
mod sstore;
mod stackonlyop;
mod stop;
mod swap;

#[cfg(test)]
mod memory_expansion_test;

use call::Call;
use calldatacopy::Calldatacopy;
use calldataload::Calldataload;
use calldatasize::Calldatasize;
use caller::Caller;
use callvalue::Callvalue;
use codecopy::Codecopy;
use codesize::Codesize;
use create::DummyCreate;
use dup::Dup;
use extcodecopy::Extcodecopy;
use extcodehash::Extcodehash;
use gasprice::GasPrice;
use logs::Log;
use mload::Mload;
use mstore::Mstore;
use origin::Origin;
use r#return::Return;
use returndatacopy::Returndatacopy;
use selfbalance::Selfbalance;
use sha3::Sha3;
use sload::Sload;
use sstore::Sstore;
use stackonlyop::StackOnlyOpcode;
use stop::Stop;
use swap::Swap;

/// Generic opcode trait which defines the logic of the
/// [`Operation`](crate::operation::Operation) that should be generated for one
/// or multiple [`ExecStep`](crate::circuit_input_builder::ExecStep) depending
/// of the [`OpcodeId`] it contains.
pub trait Opcode: Debug {
    /// Generate the associated [`MemoryOp`](crate::operation::MemoryOp)s,
    /// [`StackOp`](crate::operation::StackOp)s, and
    /// [`StorageOp`](crate::operation::StorageOp)s associated to the Opcode
    /// is implemented for.
    fn gen_associated_ops(
        &self,
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error>;
}

#[derive(Debug, Copy, Clone)]
struct Dummy;

impl Opcode for Dummy {
    fn gen_associated_ops(
        &self,
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        Ok(vec![state.new_step(&geth_steps[0])?])
    }
}

fn down_cast_to_opcode(opcode_id: &OpcodeId) -> &dyn Opcode {
    if opcode_id.is_push() {
        return &StackOnlyOpcode::<0, 1>;
    }

    match opcode_id {
        OpcodeId::STOP => &Stop,
        OpcodeId::ADD => &StackOnlyOpcode::<2, 1>,
        OpcodeId::MUL => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SUB => &StackOnlyOpcode::<2, 1>,
        OpcodeId::DIV => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SDIV => &StackOnlyOpcode::<2, 1>,
        OpcodeId::MOD => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SMOD => &StackOnlyOpcode::<2, 1>,
        OpcodeId::ADDMOD => &StackOnlyOpcode::<3, 1>,
        OpcodeId::MULMOD => &StackOnlyOpcode::<3, 1>,
        OpcodeId::EXP => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SIGNEXTEND => &StackOnlyOpcode::<2, 1>,
        OpcodeId::LT => &StackOnlyOpcode::<2, 1>,
        OpcodeId::GT => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SLT => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SGT => &StackOnlyOpcode::<2, 1>,
        OpcodeId::EQ => &StackOnlyOpcode::<2, 1>,
        OpcodeId::ISZERO => &StackOnlyOpcode::<1, 1>,
        OpcodeId::AND => &StackOnlyOpcode::<2, 1>,
        OpcodeId::OR => &StackOnlyOpcode::<2, 1>,
        OpcodeId::XOR => &StackOnlyOpcode::<2, 1>,
        OpcodeId::NOT => &StackOnlyOpcode::<1, 1>,
        OpcodeId::BYTE => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SHL => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SHR => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SAR => &StackOnlyOpcode::<2, 1>,
        OpcodeId::SHA3 => &Sha3,
        OpcodeId::ADDRESS => &StackOnlyOpcode::<0, 1>,
        OpcodeId::BALANCE => &StackOnlyOpcode::<1, 1>,
        OpcodeId::ORIGIN => &Origin,
        OpcodeId::CALLER => &Caller,
        OpcodeId::CALLVALUE => &Callvalue,
        OpcodeId::CALLDATASIZE => &Calldatasize,
        OpcodeId::CALLDATALOAD => &Calldataload,
        OpcodeId::CALLDATACOPY => &Calldatacopy,
        OpcodeId::GASPRICE => &GasPrice,
        OpcodeId::CODECOPY => &Codecopy,
        OpcodeId::CODESIZE => &Codesize,
        OpcodeId::EXTCODESIZE => &StackOnlyOpcode::<1, 1>,
        OpcodeId::EXTCODECOPY => &Extcodecopy,
        OpcodeId::RETURNDATASIZE => &StackOnlyOpcode::<0, 1>,
        OpcodeId::RETURNDATACOPY => &Returndatacopy,
        OpcodeId::EXTCODEHASH => &Extcodehash,
        OpcodeId::BLOCKHASH => &StackOnlyOpcode::<1, 1>,
        OpcodeId::COINBASE => &StackOnlyOpcode::<0, 1>,
        OpcodeId::TIMESTAMP => &StackOnlyOpcode::<0, 1>,
        OpcodeId::NUMBER => &StackOnlyOpcode::<0, 1>,
        OpcodeId::DIFFICULTY => &StackOnlyOpcode::<0, 1>,
        OpcodeId::GASLIMIT => &StackOnlyOpcode::<0, 1>,
        OpcodeId::CHAINID => &StackOnlyOpcode::<0, 1>,
        OpcodeId::SELFBALANCE => &Selfbalance,
        OpcodeId::BASEFEE => &StackOnlyOpcode::<0, 1>,
        OpcodeId::POP => &StackOnlyOpcode::<1, 0>,
        OpcodeId::MLOAD => &Mload,
        OpcodeId::MSTORE => &Mstore::<false>,
        OpcodeId::MSTORE8 => &Mstore::<true>,
        OpcodeId::SLOAD => &Sload,
        OpcodeId::SSTORE => &Sstore,
        OpcodeId::JUMP => &StackOnlyOpcode::<1, 0>,
        OpcodeId::JUMPI => &StackOnlyOpcode::<2, 0>,
        OpcodeId::PC => &StackOnlyOpcode::<0, 1>,
        OpcodeId::MSIZE => &StackOnlyOpcode::<0, 1>,
        OpcodeId::GAS => &StackOnlyOpcode::<0, 1>,
        OpcodeId::JUMPDEST => &Dummy,
        OpcodeId::DUP1 => &Dup::<1>,
        OpcodeId::DUP2 => &Dup::<2>,
        OpcodeId::DUP3 => &Dup::<3>,
        OpcodeId::DUP4 => &Dup::<4>,
        OpcodeId::DUP5 => &Dup::<5>,
        OpcodeId::DUP6 => &Dup::<6>,
        OpcodeId::DUP7 => &Dup::<7>,
        OpcodeId::DUP8 => &Dup::<8>,
        OpcodeId::DUP9 => &Dup::<9>,
        OpcodeId::DUP10 => &Dup::<10>,
        OpcodeId::DUP11 => &Dup::<11>,
        OpcodeId::DUP12 => &Dup::<12>,
        OpcodeId::DUP13 => &Dup::<13>,
        OpcodeId::DUP14 => &Dup::<14>,
        OpcodeId::DUP15 => &Dup::<15>,
        OpcodeId::DUP16 => &Dup::<16>,
        OpcodeId::SWAP1 => &Swap::<1>,
        OpcodeId::SWAP2 => &Swap::<2>,
        OpcodeId::SWAP3 => &Swap::<3>,
        OpcodeId::SWAP4 => &Swap::<4>,
        OpcodeId::SWAP5 => &Swap::<5>,
        OpcodeId::SWAP6 => &Swap::<6>,
        OpcodeId::SWAP7 => &Swap::<7>,
        OpcodeId::SWAP8 => &Swap::<8>,
        OpcodeId::SWAP9 => &Swap::<9>,
        OpcodeId::SWAP10 => &Swap::<10>,
        OpcodeId::SWAP11 => &Swap::<11>,
        OpcodeId::SWAP12 => &Swap::<12>,
        OpcodeId::SWAP13 => &Swap::<13>,
        OpcodeId::SWAP14 => &Swap::<14>,
        OpcodeId::SWAP15 => &Swap::<15>,
        OpcodeId::SWAP16 => &Swap::<16>,
        OpcodeId::LOG0 => &Log,
        OpcodeId::LOG1 => &Log,
        OpcodeId::LOG2 => &Log,
        OpcodeId::LOG3 => &Log,
        OpcodeId::LOG4 => &Log,
        // OpcodeId::CREATE => {},
        OpcodeId::CALL => &Call,
        // OpcodeId::CALLCODE => {},
        OpcodeId::RETURN => &Return,
        // OpcodeId::DELEGATECALL => {},
        // OpcodeId::CREATE2 => {},
        // OpcodeId::STATICCALL => {},
        // REVERT is almost the same as RETURN
        OpcodeId::REVERT => &Return,
        OpcodeId::SELFDESTRUCT => {
            warn!("Using dummy gen_selfdestruct_ops for opcode SELFDESTRUCT");
            &DummySelfDestruct
        }
        OpcodeId::CALLCODE | OpcodeId::DELEGATECALL | OpcodeId::STATICCALL => {
            warn!("Using dummy gen_call_ops for opcode {:?}", opcode_id);
            &DummyCall
        }
        OpcodeId::CREATE | OpcodeId::CREATE2 => {
            warn!("Using dummy gen_create_ops for opcode {:?}", opcode_id);
            &DummyCreate
        }
        _ => {
            warn!("Using dummy gen_associated_ops for opcode {:?}", opcode_id);
            &Dummy
        }
    }
}

#[allow(clippy::collapsible_else_if)]
/// Generate the associated operations according to the particular
/// [`OpcodeId`].
pub fn gen_associated_ops(
    opcode_id: &OpcodeId,
    state: &mut CircuitInputStateRef,
    geth_steps: &[GethExecStep],
) -> Result<Vec<ExecStep>, Error> {
    let opcode = down_cast_to_opcode(opcode_id);

    let memory_enabled = !geth_steps.iter().all(|s| s.memory.is_empty());
    if memory_enabled {
        assert_eq!(
            &state.call_ctx()?.memory,
            &geth_steps[0].memory,
            "last step of {:?} goes wrong",
            opcode_id
        );
    }

    let steps = opcode.gen_associated_ops(state, geth_steps)?;

    if geth_steps.len() > 1 {
        // if !geth_steps[1].memory.borrow().is_empty() {
        //     // memory trace is enabled or it is a call
        //     assert_eq!(geth_steps[1].memory.borrow().deref(), &memory, "{:?}
        // goes wrong", opcode_id); } else {
        //     if opcode_id.is_call() {
        //         if geth_steps[0].depth == geth_steps[1].depth {
        //             geth_steps[1].memory.replace(memory.clone());
        //         } else {
        //             geth_steps[1].memory.replace(Memory::default());
        //         }
        //     } else {
        //         // debug: enable trace = true
        //         // TODO: comment this when mem trace = false(auto) ..
        // heihei...         //assert_eq!(geth_steps[1].memory.borrow().
        // deref(), &memory);         geth_steps[1].memory.
        // replace(memory.clone());     }
        // }
    }

    Ok(steps)
}

pub fn gen_begin_tx_ops(state: &mut CircuitInputStateRef) -> Result<ExecStep, Error> {
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
    ] {
        state.call_context_read(&mut exec_step, call.call_id, field, value);
    }

    // Increase caller's nonce
    let caller_address = call.caller_address;
    let nonce_prev = state.sdb.increase_nonce(&caller_address);
    state.account_write(
        &mut exec_step,
        caller_address,
        AccountField::Nonce,
        (nonce_prev + 1).into(),
        nonce_prev.into(),
    )?;

    // Add caller and callee into access list
    for address in [call.caller_address, call.address] {
        state.sdb.add_account_to_access_list(address);
        state.tx_accesslist_account_write(
            &mut exec_step,
            state.tx_ctx.id(),
            address,
            true,
            false,
        )?;
    }

    // Calculate intrinsic gas cost
    let call_data_gas_cost = state
        .tx
        .input
        .iter()
        .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 });
    let intrinsic_gas_cost = if state.tx.is_create() {
        GasCost::CREATION_TX.as_u64()
    } else {
        GasCost::TX.as_u64()
    } + call_data_gas_cost;
    exec_step.gas_cost = GasCost(intrinsic_gas_cost);

    // Transfer with fee
    state.transfer_with_fee(
        &mut exec_step,
        call.caller_address,
        call.address,
        call.value,
        state.tx.gas_price * state.tx.gas,
    )?;

    // Get code_hash of callee
    let (_, callee_account) = state.sdb.get_account(&call.address);
    let code_hash = callee_account.code_hash;

    // There are 4 branches from here.
    match (
        call.is_create(),
        state.is_precompiled(&call.address),
        code_hash.to_fixed_bytes() == *EMPTY_HASH,
    ) {
        // 1. Creation transaction.
        (true, _, _) => {
            warn!("Creation transaction is left unimplemented");
            Ok(exec_step)
        }
        // 2. Call to precompiled.
        (_, true, _) => {
            warn!("Call to precompiled is left unimplemented");
            Ok(exec_step)
        }
        (_, _, is_empty_code_hash) => {
            state.account_read(
                &mut exec_step,
                call.address,
                AccountField::CodeHash,
                code_hash.to_word(),
                code_hash.to_word(),
            )?;

            // 3. Call to account with empty code.
            if is_empty_code_hash {
                warn!("Call to account with empty code is left unimplemented");
                return Ok(exec_step);
            }

            // 4. Call to account with non-empty code.
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
                (CallContextField::CodeHash, code_hash.to_word()),
            ] {
                state.call_context_read(&mut exec_step, call.call_id, field, value);
            }

            Ok(exec_step)
        }
    }
}

pub fn gen_end_tx_ops(
    state: &mut CircuitInputStateRef,
    cumulative_gas_used: &mut HashMap<usize, u64>,
) -> Result<ExecStep, Error> {
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

    let effective_refund =
        refund.min((state.tx.gas - exec_step.gas_left.0) / MAX_REFUND_QUOTIENT_OF_GAS_USED as u64);
    let (found, caller_account) = state.sdb.get_account_mut(&call.caller_address);
    if !found {
        return Err(Error::AccountNotFound(call.caller_address));
    }
    let caller_balance_prev = caller_account.balance;
    let caller_balance =
        caller_account.balance + state.tx.gas_price * (exec_step.gas_left.0 + effective_refund);

    state.account_write(
        &mut exec_step,
        call.caller_address,
        AccountField::Balance,
        caller_balance,
        caller_balance_prev,
    )?;

    let effective_tip = state.tx.gas_price - state.block.base_fee;
    let (found, coinbase_account) = state.sdb.get_account_mut(&state.block.coinbase);
    if !found {
        return Err(Error::AccountNotFound(state.block.coinbase));
    }
    let coinbase_balance_prev = coinbase_account.balance;
    let coinbase_balance =
        coinbase_account.balance + effective_tip * (state.tx.gas - exec_step.gas_left.0);
    state.account_write(
        &mut exec_step,
        state.block.coinbase,
        AccountField::Balance,
        coinbase_balance,
        coinbase_balance_prev,
    )?;

    // handle tx receipt tag
    state.tx_receipt_read(
        &mut exec_step,
        state.tx_ctx.id(),
        TxReceiptField::PostStateOrStatus,
        call.is_persistent as u64,
    )?;

    let log_id = exec_step.log_id;
    state.tx_receipt_read(
        &mut exec_step,
        state.tx_ctx.id(),
        TxReceiptField::LogLength,
        log_id as u64,
    )?;

    let gas_used = state.tx.gas - exec_step.gas_left.0;
    let mut current_cumulative_gas_used: u64 = 0;
    if state.tx_ctx.id() > 1 {
        current_cumulative_gas_used = *cumulative_gas_used.get(&(state.tx_ctx.id() - 1)).unwrap();
        // query pre tx cumulative gas
        state.tx_receipt_read(
            &mut exec_step,
            state.tx_ctx.id() - 1,
            TxReceiptField::CumulativeGasUsed,
            current_cumulative_gas_used,
        )?;
    }

    state.tx_receipt_read(
        &mut exec_step,
        state.tx_ctx.id(),
        TxReceiptField::CumulativeGasUsed,
        current_cumulative_gas_used + gas_used,
    )?;

    cumulative_gas_used.insert(state.tx_ctx.id(), current_cumulative_gas_used + gas_used);

    if !state.tx_ctx.is_last_tx() {
        state.call_context_read(
            &mut exec_step,
            state.block_ctx.rwc.0 + 1,
            CallContextField::TxId,
            (state.tx_ctx.id() + 1).into(),
        );
    }

    Ok(exec_step)
}

#[derive(Debug, Copy, Clone)]
struct DummyCall;

impl Opcode for DummyCall {
    fn gen_associated_ops(
        &self,
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        dummy_gen_call_ops(state, geth_steps)
    }
}

fn dummy_gen_call_ops(
    state: &mut CircuitInputStateRef,
    geth_steps: &[GethExecStep],
) -> Result<Vec<ExecStep>, Error> {
    let geth_step = &geth_steps[0];
    let mut exec_step = state.new_step(geth_step)?;

    let tx_id = state.tx_ctx.id();
    let call = state.parse_call(geth_step)?;

    let (_, account) = state.sdb.get_account(&call.address);
    let callee_code_hash = account.code_hash;

    let is_warm = state.sdb.check_account_in_access_list(&call.address);
    state.push_op_reversible(
        &mut exec_step,
        RW::WRITE,
        TxAccessListAccountOp {
            tx_id,
            address: call.address,
            is_warm: true,
            is_warm_prev: is_warm,
        },
    )?;

    state.push_call(call.clone());

    match (
        state.is_precompiled(&call.address),
        callee_code_hash.to_fixed_bytes() == *EMPTY_HASH,
    ) {
        // 1. Call to precompiled.
        (true, _) => Ok(vec![exec_step]),
        // 2. Call to account with empty code.
        (_, true) => {
            state.handle_return(geth_step)?;
            Ok(vec![exec_step])
        }
        // 3. Call to account with non-empty code.
        (_, false) => Ok(vec![exec_step]),
    }
}

#[derive(Debug, Copy, Clone)]
struct DummySelfDestruct;

impl Opcode for DummySelfDestruct {
    fn gen_associated_ops(
        &self,
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        dummy_gen_selfdestruct_ops(state, geth_steps)
    }
}
fn dummy_gen_selfdestruct_ops(
    state: &mut CircuitInputStateRef,
    geth_steps: &[GethExecStep],
) -> Result<Vec<ExecStep>, Error> {
    let geth_step = &geth_steps[0];
    let mut exec_step = state.new_step(geth_step)?;
    let sender = state.call()?.address;
    let receiver = geth_step.stack.last()?.to_address();

    let is_warm = state.sdb.check_account_in_access_list(&receiver);
    state.push_op_reversible(
        &mut exec_step,
        RW::WRITE,
        TxAccessListAccountOp {
            tx_id: state.tx_ctx.id(),
            address: receiver,
            is_warm: true,
            is_warm_prev: is_warm,
        },
    )?;

    let (found, receiver_account) = state.sdb.get_account(&receiver);
    if !found {
        return Err(Error::AccountNotFound(receiver));
    }
    let value = receiver_account.balance;
    state.transfer(&mut exec_step, sender, receiver, value)?;

    if state.call()?.is_persistent {
        state.sdb.destruct_account(sender);
    }

    Ok(vec![exec_step])
}
