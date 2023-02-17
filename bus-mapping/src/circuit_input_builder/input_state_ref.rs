//! CircuitInput builder tooling module.

use super::{
    get_call_memory_offset_length, get_create_init_code,
    rw::{AccountFieldTag, CallContextFieldTag, Rw, TxLogFieldTag, TxReceiptFieldTag},
    Block, BlockContext, Call, CallContext, CallKind, CodeSource, CopyEvent, ExecState, ExecStep,
    ExpEvent, Transaction, TransactionContext,
};
use crate::{
    error::{get_step_reported_error, ExecError},
    state_db::{CodeDB, StateDB},
    Error,
};
use eth_types::{
    evm_types::{
        gas_utils::memory_expansion_gas_cost, Gas, GasCost, MemoryAddress, OpcodeId, StackAddress,
    },
    Address, GethExecStep, ToAddress, ToBigEndian, ToWord, Word, H256,
};
use ethers_core::utils::{get_contract_address, get_create2_address};
use std::cmp::max;

/// Reference to the internal state of the CircuitInputBuilder in a particular
/// [`ExecStep`].
pub struct CircuitInputStateRef<'a> {
    /// StateDB
    pub sdb: &'a mut StateDB,
    /// CodeDB
    pub code_db: &'a mut CodeDB,
    /// Block
    pub block: &'a mut Block,
    /// Block Context
    pub block_ctx: &'a mut BlockContext,
    /// Transaction
    pub tx: &'a mut Transaction,
    /// Transaction Context
    pub tx_ctx: &'a mut TransactionContext,
}

impl<'a> CircuitInputStateRef<'a> {
    fn increment_rw_counter(&mut self) -> usize {
        let rwc = self.block_ctx.rwc;
        self.block_ctx.rwc += 1;
        rwc
    }

    /// Create a new step from a `GethExecStep`
    pub fn new_step(&self, geth_step: &GethExecStep) -> Result<ExecStep, Error> {
        let call_ctx = self.tx_ctx.call_ctx()?;

        Ok(ExecStep::new(
            geth_step,
            call_ctx,
            self.block_ctx.rwc,
            call_ctx.reversible_write_counter,
            self.tx_ctx.log_id,
        ))
    }

    /// Create a new BeginTx step
    pub fn new_begin_tx_step(&self) -> ExecStep {
        ExecStep {
            exec_state: ExecState::BeginTx,
            gas_left: Gas(self.tx.gas),
            rwc: self.block_ctx.rwc,
            ..Default::default()
        }
    }

    /// Create a new EndTx step
    pub fn new_end_tx_step(&self) -> ExecStep {
        let prev_step = self
            .tx
            .steps()
            .last()
            .expect("steps should have at least one BeginTx step");
        ExecStep {
            exec_state: ExecState::EndTx,
            gas_left: if prev_step.error.is_none() {
                Gas(prev_step.gas_left.0 - prev_step.gas_cost.0)
            } else {
                // consume all remaining gas when non revert err happens
                Gas(0)
            },
            rwc: self.block_ctx.rwc,
            // For tx without code execution
            reversible_write_counter: if let Some(call_ctx) = self.tx_ctx.calls().last() {
                call_ctx.reversible_write_counter
            } else {
                0
            },
            log_id: self.tx_ctx.log_id,
            ..Default::default()
        }
    }

    /// TODO:
    fn push_op<const REVERSIBLE: bool>(
        &mut self,
        step: &mut ExecStep,
        rw: Rw,
    ) -> Result<(), Error> {
        if rw.is_write() {
            self.apply_rw(&rw);
        }
        let rw_idx = self.block.container.push(rw);
        step.bus_mapping_instance.push(rw_idx);

        if REVERSIBLE {
            // Increase reversible_write_counter
            self.call_ctx_mut()?.reversible_write_counter += 1;

            // Add the operation into reversible_ops if this call is not persistent
            if !self.call()?.is_persistent {
                self.tx_ctx
                    .reversion_groups
                    .last_mut()
                    .expect("reversion_groups should not be empty for non-persistent call")
                    .rw_indices
                    .push((self.tx.steps().len(), rw_idx));
            }
        }
        Ok(())
    }

    /// TODO:
    pub fn call_context_read(
        &mut self,
        step: &mut ExecStep,
        call_id: usize,
        field_tag: CallContextFieldTag,
        value: Word,
    ) {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::CallContext {
                rw_counter,
                is_write: false,
                call_id,
                field_tag,
                value,
            },
        )
        .unwrap();
    }

    /// TODO:
    pub fn call_context_write(
        &mut self,
        step: &mut ExecStep,
        call_id: usize,
        field_tag: CallContextFieldTag,
        value: Word,
    ) {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::CallContext {
                rw_counter,
                is_write: true,
                call_id,
                field_tag,
                value,
            },
        )
        .unwrap();
    }

    /// TODO:
    pub fn memory_read(
        &mut self,
        step: &mut ExecStep,
        call_id: usize,
        memory_address: MemoryAddress,
        byte: u8,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::Memory {
                rw_counter,
                is_write: false,
                call_id,
                memory_address: memory_address.0 as u64,
                byte,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn memory_write(
        &mut self,
        step: &mut ExecStep,
        call_id: usize,
        memory_address: MemoryAddress,
        byte: u8,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::Memory {
                rw_counter,
                is_write: true,
                call_id,
                memory_address: memory_address.0 as u64,
                byte,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn stack_write(
        &mut self,
        step: &mut ExecStep,
        stack_pointer: StackAddress,
        value: Word,
    ) -> Result<(), Error> {
        let call_id = self.call()?.call_id;
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::Stack {
                rw_counter,
                is_write: true,
                call_id,
                stack_pointer: stack_pointer.0,
                value,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn stack_read(
        &mut self,
        step: &mut ExecStep,
        stack_pointer: StackAddress,
        value: Word,
    ) -> Result<(), Error> {
        let call_id = self.call()?.call_id;
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::Stack {
                rw_counter,
                is_write: false,
                call_id,
                stack_pointer: stack_pointer.0,
                value,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn account_read(
        &mut self,
        step: &mut ExecStep,
        account_address: Address,
        field_tag: AccountFieldTag,
        value: Word,
        value_prev: Word,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::Account {
                rw_counter,
                is_write: false,
                account_address,
                field_tag,
                value,
                value_prev,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn account_write<const REVERSIBLE: bool>(
        &mut self,
        step: &mut ExecStep,
        account_address: Address,
        field_tag: AccountFieldTag,
        value: Word,
        value_prev: Word,
    ) -> Result<(), Error> {
        let rw = Rw::Account {
            rw_counter: self.increment_rw_counter(),
            is_write: true,
            account_address,
            field_tag,
            value,
            value_prev,
        };
        self.push_op::<REVERSIBLE>(step, rw)?;
        Ok(())
    }

    /// TODO:
    pub fn account_storage_read(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        account_address: Address,
        storage_key: Word,
        value: Word,
        committed_value: Word,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::AccountStorage {
                rw_counter,
                is_write: false,
                tx_id,
                account_address,
                storage_key,
                value,
                value_prev: value,
                committed_value,
            },
        )?;
        Ok(())
    }

    /// TODO:
    #[allow(clippy::too_many_arguments)]
    pub fn account_storage_write<const REVERSIBLE: bool>(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        account_address: Address,
        storage_key: Word,
        value: Word,
        value_prev: Word,
        committed_value: Word,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        let rw = Rw::AccountStorage {
            rw_counter,
            is_write: true,
            tx_id,
            account_address,
            storage_key,
            value,
            value_prev,
            committed_value,
        };
        self.push_op::<REVERSIBLE>(step, rw)?;
        Ok(())
    }

    /// TODO:
    pub fn tx_log_write(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        log_id: usize,
        field_tag: TxLogFieldTag,
        index: usize,
        value: Word,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::TxLog {
                rw_counter,
                is_write: true,
                tx_id,
                log_id: log_id as u64,
                field_tag,
                index,
                value,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_receipt_read(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        field_tag: TxReceiptFieldTag,
        value: u64,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::TxReceipt {
                rw_counter,
                is_write: false,
                tx_id,
                field_tag,
                value,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_receipt_write(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        field_tag: TxReceiptFieldTag,
        value: u64,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::TxReceipt {
                rw_counter,
                is_write: true,
                tx_id,
                field_tag,
                value,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_accesslist_account_read(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        account_address: Address,
        is_warm: bool,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::TxAccessListAccount {
                rw_counter,
                is_write: false,
                tx_id,
                account_address,
                is_warm,
                is_warm_prev: is_warm,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_accesslist_account_write<const REVERSIBLE: bool>(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        account_address: Address,
        is_warm: bool,
        is_warm_prev: bool,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<REVERSIBLE>(
            step,
            Rw::TxAccessListAccount {
                rw_counter,
                is_write: true,
                tx_id,
                account_address,
                is_warm,
                is_warm_prev,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_accesslist_account_storage_read(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        account_address: Address,
        storage_key: Word,
        is_warm: bool,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::TxAccessListAccountStorage {
                rw_counter,
                is_write: false,
                tx_id,
                account_address,
                storage_key,
                is_warm,
                is_warm_prev: is_warm,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_accesslist_account_storage_write<const REVERSIBLE: bool>(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        account_address: Address,
        storage_key: Word,
        is_warm: bool,
        is_warm_prev: bool,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<REVERSIBLE>(
            step,
            Rw::TxAccessListAccountStorage {
                rw_counter,
                is_write: true,
                tx_id,
                account_address,
                storage_key,
                is_warm,
                is_warm_prev,
            },
        )?;
        Ok(())
    }

    /// Push 2 reversible [`Rw::Account`] to update `sender` and `receiver`'s
    /// balance by `value`, with `sender` being extraly charged with `fee`.
    pub fn transfer_with_fee(
        &mut self,
        step: &mut ExecStep,
        sender: Address,
        receiver: Address,
        value: Word,
        fee: Word,
    ) -> Result<(), Error> {
        let (found, sender_account) = self.sdb.get_account(&sender);
        if !found {
            return Err(Error::AccountNotFound(sender));
        }
        let sender_balance_prev = sender_account.balance;
        let sender_balance = sender_account.balance - value - fee;
        let rw_counter = self.increment_rw_counter();
        self.push_op::<true>(
            step,
            Rw::Account {
                rw_counter,
                is_write: true,
                account_address: sender,
                field_tag: AccountFieldTag::Balance,
                value: sender_balance,
                value_prev: sender_balance_prev,
            },
        )?;

        let (_found, receiver_account) = self.sdb.get_account(&receiver);
        let receiver_balance_prev = receiver_account.balance;
        let receiver_balance = receiver_account.balance + value;
        let rw_counter = self.increment_rw_counter();
        self.push_op::<true>(
            step,
            Rw::Account {
                rw_counter,
                is_write: true,
                account_address: receiver,
                field_tag: AccountFieldTag::Balance,
                value: receiver_balance,
                value_prev: receiver_balance_prev,
            },
        )?;

        Ok(())
    }

    /// TODO:
    pub fn tx_refund_read(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        refund: u64,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<false>(
            step,
            Rw::TxRefund {
                rw_counter,
                is_write: false,
                tx_id,
                value: refund,
                value_prev: refund,
            },
        )?;
        Ok(())
    }

    /// TODO:
    pub fn tx_refund_write(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        refund: u64,
        refund_prev: u64,
    ) -> Result<(), Error> {
        let rw_counter = self.increment_rw_counter();
        self.push_op::<true>(
            step,
            Rw::TxRefund {
                rw_counter,
                is_write: true,
                tx_id,
                value: refund,
                value_prev: refund_prev,
            },
        )?;
        Ok(())
    }

    /// Same functionality with `transfer_with_fee` but with `fee` set zero.
    pub fn transfer(
        &mut self,
        step: &mut ExecStep,
        sender: Address,
        receiver: Address,
        value: Word,
    ) -> Result<(), Error> {
        self.transfer_with_fee(step, sender, receiver, value, Word::zero())
    }

    /// Fetch and return code for the given code hash from the code DB.
    pub fn code(&self, code_hash: H256) -> Result<Vec<u8>, Error> {
        self.code_db
            .0
            .get(&code_hash)
            .cloned()
            .ok_or(Error::CodeNotFound(code_hash))
    }

    /// Reference to the caller's Call
    pub fn caller(&self) -> Result<&Call, Error> {
        self.tx_ctx
            .caller_index()
            .map(|caller_idx| &self.tx.calls()[caller_idx])
    }

    /// Mutable reference to the current call's caller Call
    pub fn caller_mut(&mut self) -> Result<&mut Call, Error> {
        self.tx_ctx
            .caller_index()
            .map(|caller_idx| &mut self.tx.calls_mut()[caller_idx])
    }

    /// Reference to the current Call
    pub fn call(&self) -> Result<&Call, Error> {
        self.tx_ctx
            .call_index()
            .map(|call_idx| &self.tx.calls()[call_idx])
    }

    /// Mutable reference to the current Call
    pub fn call_mut(&mut self) -> Result<&mut Call, Error> {
        self.tx_ctx
            .call_index()
            .map(|call_idx| &mut self.tx.calls_mut()[call_idx])
    }

    /// Reference to the current CallContext
    pub fn caller_ctx(&self) -> Result<&CallContext, Error> {
        self.tx_ctx.caller_ctx()
    }

    /// Reference to the current CallContext
    pub fn call_ctx(&self) -> Result<&CallContext, Error> {
        self.tx_ctx.call_ctx()
    }

    /// Mutable reference to the call CallContext
    pub fn call_ctx_mut(&mut self) -> Result<&mut CallContext, Error> {
        self.tx_ctx.call_ctx_mut()
    }

    /// Mutable reference to the caller CallContext
    pub fn caller_ctx_mut(&mut self) -> Result<&mut CallContext, Error> {
        self.tx_ctx
            .calls
            .iter_mut()
            .rev()
            .nth(1)
            .ok_or(Error::InternalError("caller id not found in call map"))
    }

    /// Push a new [`Call`] into the [`Transaction`], and add its index and
    /// [`CallContext`] in the `call_stack` of the [`TransactionContext`]
    pub fn push_call(&mut self, call: Call) {
        let current_call = self.call_ctx().expect("current call not found");
        let call_data = match call.kind {
            CallKind::Call | CallKind::CallCode | CallKind::DelegateCall | CallKind::StaticCall => {
                current_call
                    .memory
                    .read_chunk(call.call_data_offset.into(), call.call_data_length.into())
            }
            CallKind::Create | CallKind::Create2 => Vec::new(),
        };

        let call_id = call.call_id;
        let call_idx = self.tx.calls().len();

        self.tx_ctx.push_call_ctx(call_idx, call_data);
        self.tx.push_call(call);

        self.block_ctx
            .call_map
            .insert(call_id, (self.block.txs.len(), call_idx));
    }

    /// Return the contract address of a CREATE step.  This is calculated by
    /// inspecting the current address and its nonce from the StateDB.
    pub(crate) fn create_address(&self) -> Result<Address, Error> {
        let sender = self.call()?.address;
        let (found, account) = self.sdb.get_account(&sender);
        if !found {
            return Err(Error::AccountNotFound(sender));
        }
        Ok(get_contract_address(sender, account.nonce))
    }

    /// Return the contract address of a CREATE2 step.  This is calculated
    /// deterministically from the arguments in the stack.
    pub(crate) fn create2_address(&self, step: &GethExecStep) -> Result<Address, Error> {
        let salt = step.stack.nth_last(3)?;
        let call_ctx = self.call_ctx()?;
        let init_code = get_create_init_code(call_ctx, step)?.to_vec();
        Ok(get_create2_address(
            self.call()?.address,
            salt.to_be_bytes().to_vec(),
            init_code,
        ))
    }

    /// Check if address is a precompiled or not.
    pub fn is_precompiled(&self, address: &Address) -> bool {
        address.0[0..19] == [0u8; 19] && (1..=9).contains(&address.0[19])
    }

    /// Parse [`Call`] from a *CALL*/CREATE* step.
    pub fn parse_call(&mut self, step: &GethExecStep) -> Result<Call, Error> {
        let is_success = *self
            .tx_ctx
            .call_is_success
            .get(self.tx.calls().len())
            .unwrap();
        let kind = CallKind::try_from(step.op)?;
        let caller = self.call()?;
        let caller_ctx = self.call_ctx()?;

        let (caller_address, address, value) = match kind {
            CallKind::Call => (
                caller.address,
                step.stack.nth_last(1)?.to_address(),
                step.stack.nth_last(2)?,
            ),
            CallKind::CallCode => (caller.address, caller.address, step.stack.nth_last(2)?),
            CallKind::DelegateCall => (caller.caller_address, caller.address, caller.value),
            CallKind::StaticCall => (
                caller.address,
                step.stack.nth_last(1)?.to_address(),
                Word::zero(),
            ),
            CallKind::Create => (caller.address, self.create_address()?, step.stack.last()?),
            CallKind::Create2 => (
                caller.address,
                self.create2_address(step)?,
                step.stack.last()?,
            ),
        };

        let (code_source, code_hash) = match kind {
            CallKind::Create | CallKind::Create2 => {
                let init_code = get_create_init_code(caller_ctx, step)?.to_vec();
                let code_hash = self.code_db.insert(init_code);
                (CodeSource::Memory, code_hash)
            }
            _ => {
                let code_address = match kind {
                    CallKind::CallCode | CallKind::DelegateCall => {
                        step.stack.nth_last(1)?.to_address()
                    }
                    _ => address,
                };
                let (found, account) = self.sdb.get_account(&code_address);
                if !found {
                    return Err(Error::AccountNotFound(code_address));
                }
                (CodeSource::Address(code_address), account.code_hash)
            }
        };

        let (call_data_offset, call_data_length, return_data_offset, return_data_length) =
            match kind {
                CallKind::Call | CallKind::CallCode => {
                    let call_data = get_call_memory_offset_length(step, 3)?;
                    let return_data = get_call_memory_offset_length(step, 5)?;
                    (call_data.0, call_data.1, return_data.0, return_data.1)
                }
                CallKind::DelegateCall | CallKind::StaticCall => {
                    let call_data = get_call_memory_offset_length(step, 2)?;
                    let return_data = get_call_memory_offset_length(step, 4)?;
                    (call_data.0, call_data.1, return_data.0, return_data.1)
                }
                CallKind::Create | CallKind::Create2 => (0, 0, 0, 0),
            };

        let caller = self.call()?;
        let call = Call {
            call_id: self.block_ctx.rwc,
            caller_id: caller.call_id,
            last_callee_id: 0,
            kind,
            is_static: kind == CallKind::StaticCall || caller.is_static,
            is_root: false,
            is_persistent: caller.is_persistent && is_success,
            is_success,
            rw_counter_end_of_reversion: 0,
            caller_address,
            address,
            code_source,
            code_hash,
            depth: caller.depth + 1,
            value,
            call_data_offset,
            call_data_length,
            return_data_offset,
            return_data_length,
            last_callee_return_data_offset: 0,
            last_callee_return_data_length: 0,
        };

        Ok(call)
    }

    /// Return the reverted version of an op by op_ref only if the original op
    /// was reversible.
    fn get_rev_rw_by_idx(&mut self, rw_idx: usize) -> Option<Rw> {
        match self.block.container[rw_idx] {
            Rw::Account {
                is_write: true,
                account_address,
                field_tag,
                value,
                value_prev,
                ..
            } => {
                let rw_counter = self.increment_rw_counter();
                Some(Rw::Account {
                    rw_counter,
                    is_write: true,
                    account_address,
                    field_tag,
                    value: value_prev,
                    value_prev: value,
                })
            }
            Rw::AccountStorage {
                is_write: true,
                account_address,
                storage_key,
                value,
                value_prev,
                tx_id,
                committed_value,
                ..
            } => {
                let rw_counter = self.increment_rw_counter();
                Some(Rw::AccountStorage {
                    rw_counter,
                    is_write: true,
                    account_address,
                    storage_key,
                    value: value_prev,
                    value_prev: value,
                    tx_id,
                    committed_value,
                })
            }
            Rw::TxAccessListAccount {
                is_write: true,
                tx_id,
                account_address,
                is_warm,
                is_warm_prev,
                ..
            } => {
                let rw_counter = self.increment_rw_counter();
                Some(Rw::TxAccessListAccount {
                    rw_counter,
                    is_write: true,
                    tx_id,
                    account_address,
                    is_warm: is_warm_prev,
                    is_warm_prev: is_warm,
                })
            }
            Rw::TxAccessListAccountStorage {
                is_write: true,
                tx_id,
                account_address,
                storage_key,
                is_warm,
                is_warm_prev,
                ..
            } => {
                let rw_counter = self.increment_rw_counter();
                Some(Rw::TxAccessListAccountStorage {
                    rw_counter,
                    is_write: true,
                    tx_id,
                    account_address,
                    storage_key,
                    is_warm: is_warm_prev,
                    is_warm_prev: is_warm,
                })
            }
            Rw::TxRefund {
                is_write: true,
                tx_id,
                value,
                value_prev,
                ..
            } => {
                let rw_counter = self.increment_rw_counter();
                Some(Rw::TxRefund {
                    rw_counter,
                    is_write: true,
                    tx_id,
                    value: value_prev,
                    value_prev: value,
                })
            }
            _ => None,
        }
    }

    /// Apply op to state.
    fn apply_rw(&mut self, rw: &Rw) {
        match rw {
            Rw::Account {
                is_write: true,
                account_address,
                field_tag,
                value,
                ..
            } => {
                let (_, account) = self.sdb.get_account_mut(account_address);
                match field_tag {
                    AccountFieldTag::Nonce => account.nonce = *value,
                    AccountFieldTag::Balance => account.balance = *value,
                    AccountFieldTag::CodeHash => account.code_hash = value.to_be_bytes().into(),
                    _ => {}
                }
            }
            Rw::AccountStorage {
                is_write: true,
                account_address,
                storage_key,
                value,
                ..
            } => self.sdb.set_storage(account_address, storage_key, value),
            Rw::TxAccessListAccount {
                is_write: true,
                account_address,
                is_warm,
                is_warm_prev,
                ..
            } => {
                if !is_warm_prev && *is_warm {
                    self.sdb.add_account_to_access_list(*account_address);
                }
                if *is_warm_prev && !is_warm {
                    self.sdb.remove_account_from_access_list(account_address);
                }
            }
            Rw::TxAccessListAccountStorage {
                is_write: true,
                account_address,
                storage_key,
                is_warm,
                is_warm_prev,
                ..
            } => {
                if !is_warm_prev && *is_warm {
                    self.sdb
                        .add_account_storage_to_access_list((*account_address, *storage_key));
                }
                if *is_warm_prev && !is_warm {
                    self.sdb
                        .remove_account_storage_from_access_list(&(*account_address, *storage_key));
                }
            }
            Rw::TxRefund {
                is_write: true,
                value,
                ..
            } => {
                self.sdb.set_refund(*value);
            }
            _ => {}
        };
    }

    /// Handle a reversion group
    fn handle_reversion(&mut self) {
        let reversion_group = self
            .tx_ctx
            .reversion_groups
            .pop()
            .expect("reversion_groups should not be empty for non-persistent call");

        // Apply reversions
        for (step_index, rw_idx) in reversion_group.rw_indices.iter().rev().copied() {
            if let Some(rw) = self.get_rev_rw_by_idx(rw_idx) {
                self.apply_rw(&rw);
                let rev_rw_idx = self.block.container.push(rw);
                self.tx.steps_mut()[step_index]
                    .bus_mapping_instance
                    .push(rev_rw_idx);
            }
        }

        // Set calls' `rw_counter_end_of_reversion`
        let rwc = self.block_ctx.rwc - 1;
        for (call_idx, reversible_write_counter_offset) in reversion_group.calls {
            self.tx.calls_mut()[call_idx].rw_counter_end_of_reversion =
                rwc - reversible_write_counter_offset;
        }
    }

    /// Handle a return step caused by any opcode that causes a return to the
    /// previous call context.
    pub fn handle_return(&mut self, step: &GethExecStep) -> Result<(), Error> {
        // handle return_data
        let (return_data_offset, return_data_length) = {
            if !self.call()?.is_root {
                let (offset, length) = match step.op {
                    OpcodeId::RETURN | OpcodeId::REVERT => {
                        let offset = step.stack.nth_last(0)?.as_usize();
                        let length = step.stack.nth_last(1)?.as_usize();

                        // At the moment it conflicts with `call_ctx` and `caller_ctx`.
                        let callee_memory = self.call_ctx()?.memory.clone();
                        let caller_ctx = self.caller_ctx_mut()?;
                        caller_ctx.return_data.resize(length, 0);
                        if length != 0 {
                            caller_ctx.return_data[0..length]
                                .copy_from_slice(&callee_memory.0[offset..offset + length]);
                        }
                        (offset, length)
                    }
                    _ => {
                        let caller_ctx = self.caller_ctx_mut()?;
                        caller_ctx.return_data.truncate(0);
                        (0, 0)
                    }
                };

                (offset.try_into().unwrap(), length.try_into().unwrap())
            } else {
                (0, 0)
            }
        };

        let call = self.call()?.clone();
        let call_ctx = self.call_ctx()?;

        // Store deployed code if it's a successful create
        if call.is_create() && call.is_success && step.op == OpcodeId::RETURN {
            let offset = step.stack.nth_last(0)?;
            let length = step.stack.nth_last(1)?;
            let code = call_ctx
                .memory
                .read_chunk(offset.low_u64().into(), length.low_u64().into());
            let code_hash = self.code_db.insert(code);
            let (found, callee_account) = self.sdb.get_account_mut(&call.address);
            if !found {
                return Err(Error::AccountNotFound(call.address));
            }
            callee_account.code_hash = code_hash;
        }

        // Handle reversion if this call doesn't end successfully
        if !call.is_success {
            self.handle_reversion();
        }

        // If current call has caller.
        if let Ok(caller) = self.caller_mut() {
            caller.last_callee_id = call.call_id;
            caller.last_callee_return_data_length = return_data_length;
            caller.last_callee_return_data_offset = return_data_offset;
        }

        self.tx_ctx.pop_call_ctx();

        Ok(())
    }

    /// Bus mapping for the RestoreContextGadget as used in RETURN.
    // TODO: unify this with restore context bus mapping for STOP.
    // TODO: unify this with the `handle return function above.`
    pub fn handle_restore_context(
        &mut self,
        steps: &[GethExecStep],
        exec_step: &mut ExecStep,
    ) -> Result<(), Error> {
        let call = self.call()?.clone();
        let caller = self.caller()?.clone();
        self.call_context_read(
            exec_step,
            call.call_id,
            CallContextFieldTag::CallerId,
            caller.call_id.into(),
        );

        let geth_step = &steps[0];
        let geth_step_next = &steps[1];

        let [last_callee_return_data_offset, last_callee_return_data_length] = match geth_step.op {
            OpcodeId::STOP => [Word::zero(); 2],
            OpcodeId::REVERT | OpcodeId::RETURN => {
                let offset = geth_step.stack.nth_last(0)?;
                let length = geth_step.stack.nth_last(1)?;
                // This is the convention we are using for memory addresses so that there is no
                // memory expansion cost when the length is 0.
                if length.is_zero() {
                    [Word::zero(); 2]
                } else {
                    [offset, length]
                }
            }
            _ => unreachable!(),
        };

        let curr_memory_word_size = (exec_step.memory_size as u64) / 32;
        let next_memory_word_size = if !last_callee_return_data_length.is_zero() {
            std::cmp::max(
                (last_callee_return_data_offset + last_callee_return_data_length + 31).as_u64()
                    / 32,
                curr_memory_word_size,
            )
        } else {
            curr_memory_word_size
        };

        let memory_expansion_gas_cost =
            memory_expansion_gas_cost(curr_memory_word_size, next_memory_word_size);
        let code_deposit_cost = if call.is_create() && call.is_success {
            GasCost::CODE_DEPOSIT_BYTE_COST.as_u64() * last_callee_return_data_length.as_u64()
        } else {
            0
        };
        let gas_refund = geth_step.gas.0 - memory_expansion_gas_cost - code_deposit_cost;

        let caller_gas_left = geth_step_next.gas.0 - gas_refund;

        for (field, value) in [
            (CallContextFieldTag::IsRoot, (caller.is_root as u64).into()),
            (
                CallContextFieldTag::IsCreate,
                (caller.is_create() as u64).into(),
            ),
            (CallContextFieldTag::CodeHash, caller.code_hash.to_word()),
            (
                CallContextFieldTag::ProgramCounter,
                geth_step_next.pc.0.into(),
            ),
            (
                CallContextFieldTag::StackPointer,
                geth_step_next.stack.stack_pointer().0.into(),
            ),
            (CallContextFieldTag::GasLeft, caller_gas_left.into()),
            (
                CallContextFieldTag::MemorySize,
                self.caller_ctx()?.memory.word_size().into(),
            ),
            (
                CallContextFieldTag::ReversibleWriteCounter,
                self.caller_ctx()?.reversible_write_counter.into(),
            ),
        ] {
            self.call_context_read(exec_step, caller.call_id, field, value);
        }

        for (field, value) in [
            (CallContextFieldTag::LastCalleeId, call.call_id.into()),
            (
                CallContextFieldTag::LastCalleeReturnDataOffset,
                last_callee_return_data_offset,
            ),
            (
                CallContextFieldTag::LastCalleeReturnDataLength,
                last_callee_return_data_length,
            ),
        ] {
            self.call_context_write(exec_step, caller.call_id, field, value);
        }

        Ok(())
    }

    /// Push a copy event to the state.
    pub fn push_copy(&mut self, event: CopyEvent) {
        self.block.add_copy_event(event);
    }

    /// Push a exponentiation event to the state.
    pub fn push_exponentiation(&mut self, event: ExpEvent) {
        self.block.add_exp_event(event)
    }

    pub(crate) fn get_step_err(
        &self,
        step: &GethExecStep,
        next_step: Option<&GethExecStep>,
    ) -> Result<Option<ExecError>, Error> {
        if let Some(error) = &step.error {
            return Ok(Some(get_step_reported_error(&step.op, error)));
        }

        if matches!(step.op, OpcodeId::INVALID(_)) {
            return Ok(Some(ExecError::InvalidOpcode));
        }

        // When last step has opcodes that halt, there's no error.
        if matches!(next_step, None)
            && matches!(
                step.op,
                OpcodeId::STOP | OpcodeId::RETURN | OpcodeId::REVERT | OpcodeId::SELFDESTRUCT
            )
        {
            return Ok(None);
        }

        let next_depth = next_step.map(|s| s.depth).unwrap_or(0);
        let next_result = next_step
            .map(|s| s.stack.last().unwrap_or_else(|_| Word::zero()))
            .unwrap_or_else(Word::zero);

        let call = self.call()?;
        let call_ctx = self.call_ctx()?;
        // get value first if call/create
        let value = match step.op {
            OpcodeId::CALL | OpcodeId::CALLCODE => step.stack.nth_last(2)?,
            OpcodeId::CREATE | OpcodeId::CREATE2 => step.stack.nth_last(0)?,
            _ => Word::zero(),
        };

        // Return from a call with a failure
        if step.depth == next_depth + 1 && next_result.is_zero() {
            if !matches!(step.op, OpcodeId::RETURN) {
                // Without calling RETURN
                return Ok(match step.op {
                    OpcodeId::JUMP | OpcodeId::JUMPI => Some(ExecError::InvalidJump),
                    OpcodeId::RETURNDATACOPY => Some(ExecError::ReturnDataOutOfBounds),
                    // Break write protection (CALL with value will be handled below)
                    OpcodeId::SSTORE
                    | OpcodeId::CREATE
                    | OpcodeId::CREATE2
                    | OpcodeId::SELFDESTRUCT
                    | OpcodeId::LOG0
                    | OpcodeId::LOG1
                    | OpcodeId::LOG2
                    | OpcodeId::LOG3
                    | OpcodeId::LOG4
                        if call.is_static =>
                    {
                        Some(ExecError::WriteProtection)
                    }
                    OpcodeId::CALL if call.is_static && !value.is_zero() => {
                        Some(ExecError::WriteProtection)
                    }

                    OpcodeId::REVERT => None,
                    _ => {
                        return Err(Error::UnexpectedExecStepError(
                            "call failure without return",
                            step.clone(),
                        ));
                    }
                });
            } else {
                // Return from a {CREATE, CREATE2} with a failure, via RETURN
                if !call.is_root && call.is_create() {
                    let offset = step.stack.nth_last(0)?;
                    let length = step.stack.nth_last(1)?;
                    if length > Word::from(0x6000u64) {
                        return Ok(Some(ExecError::MaxCodeSizeExceeded));
                    } else if length > Word::zero()
                        && !call_ctx.memory.is_empty()
                        && call_ctx.memory.0.get(offset.low_u64() as usize) == Some(&0xef)
                    {
                        return Ok(Some(ExecError::InvalidCreationCode));
                    } else if Word::from(200u64) * length > Word::from(step.gas.0) {
                        return Ok(Some(ExecError::CodeStoreOutOfGas));
                    } else {
                        return Err(Error::UnexpectedExecStepError(
                            "failure in RETURN from {CREATE, CREATE2}",
                            step.clone(),
                        ));
                    }
                } else {
                    return Err(Error::UnexpectedExecStepError(
                        "failure in RETURN",
                        step.clone(),
                    ));
                }
            }
        }

        // Return from a call via RETURN or STOP and having a success result is
        // OK.

        // Return from a call without calling RETURN or STOP and having success
        // is unexpected.
        if step.depth == next_depth + 1
            && next_result != Word::zero()
            && !matches!(
                step.op,
                OpcodeId::RETURN | OpcodeId::STOP | OpcodeId::SELFDESTRUCT
            )
        {
            return Err(Error::UnexpectedExecStepError(
                "success result without {RETURN, STOP, SELFDESTRUCT}",
                step.clone(),
            ));
        }

        // The *CALL*/CREATE* code was not executed
        let next_pc = next_step.map(|s| s.pc.0).unwrap_or(1);
        if matches!(
            step.op,
            OpcodeId::CALL
                | OpcodeId::CALLCODE
                | OpcodeId::DELEGATECALL
                | OpcodeId::STATICCALL
                | OpcodeId::CREATE
                | OpcodeId::CREATE2
        ) && next_result.is_zero()
            && next_pc != 0
        {
            if step.depth == 1025 {
                return Ok(Some(ExecError::Depth));
            }

            let sender = self.call()?.address;
            let (found, account) = self.sdb.get_account(&sender);
            if !found {
                return Err(Error::AccountNotFound(sender));
            }
            if account.balance < value {
                return Ok(Some(ExecError::InsufficientBalance));
            }

            // Address collision
            if matches!(step.op, OpcodeId::CREATE | OpcodeId::CREATE2) {
                let address = match step.op {
                    OpcodeId::CREATE => self.create_address()?,
                    OpcodeId::CREATE2 => self.create2_address(step)?,
                    _ => unreachable!(),
                };
                let (found, _) = self.sdb.get_account(&address);
                if found {
                    return Ok(Some(ExecError::ContractAddressCollision));
                }
            }

            return Err(Error::UnexpectedExecStepError(
                "*CALL*/CREATE* code not executed",
                step.clone(),
            ));
        }

        Ok(None)
    }

    /// Expand memory of the call context when entering a new call context in
    /// case the call arguments or return arguments go beyond the call
    /// context current memory.
    pub(crate) fn call_expand_memory(
        &mut self,
        args_offset: usize,
        args_length: usize,
        ret_offset: usize,
        ret_length: usize,
    ) -> Result<(), Error> {
        let call_ctx = self.call_ctx_mut()?;
        let args_minimal = if args_length != 0 {
            args_offset + args_length
        } else {
            0
        };
        let ret_minimal = if ret_length != 0 {
            ret_offset + ret_length
        } else {
            0
        };
        if args_minimal != 0 || ret_minimal != 0 {
            let minimal_length = max(args_minimal, ret_minimal);
            call_ctx.memory.extend_at_least(minimal_length);
        }
        Ok(())
    }

    /// gen bus mapping operations for context restore purpose
    pub(crate) fn gen_restore_context_ops(
        &mut self,
        exec_step: &mut ExecStep,
        geth_steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let geth_step = &geth_steps[0];
        let call = self.call()?.clone();
        if !call.is_success {
            // add call failure ops for exception cases
            self.call_context_read(
                exec_step,
                call.call_id,
                CallContextFieldTag::IsSuccess,
                0u64.into(),
            );

            //Even call.rw_counter_end_of_reversion is zero for now, it will set in
            //set_value_ops_call_context_rwc_eor later
            // if call fails, no matter root or internal, read RwCounterEndOfReversion for
            // circuit constraint.
            self.call_context_read(
                exec_step,
                call.call_id,
                CallContextFieldTag::RwCounterEndOfReversion,
                call.rw_counter_end_of_reversion.into(),
            );

            if call.is_root {
                return Ok(());
            }
        }

        let caller = self.caller()?.clone();
        self.call_context_read(
            exec_step,
            call.call_id,
            CallContextFieldTag::CallerId,
            caller.call_id.into(),
        );

        let geth_step_next = &geth_steps[1];
        let caller_ctx = self.caller_ctx()?;
        let caller_gas_left = if call.is_success {
            geth_step_next.gas.0 - geth_step.gas.0
        } else {
            geth_step_next.gas.0
        };

        for (field, value) in [
            (CallContextFieldTag::IsRoot, (caller.is_root as u64).into()),
            (
                CallContextFieldTag::IsCreate,
                (caller.is_create() as u64).into(),
            ),
            (CallContextFieldTag::CodeHash, caller.code_hash.to_word()),
            (
                CallContextFieldTag::ProgramCounter,
                geth_step_next.pc.0.into(),
            ),
            (
                CallContextFieldTag::StackPointer,
                geth_step_next.stack.stack_pointer().0.into(),
            ),
            (CallContextFieldTag::GasLeft, caller_gas_left.into()),
            (
                CallContextFieldTag::MemorySize,
                caller_ctx.memory.word_size().into(),
            ),
            (
                CallContextFieldTag::ReversibleWriteCounter,
                self.caller_ctx()?.reversible_write_counter.into(),
            ),
        ] {
            self.call_context_read(exec_step, caller.call_id, field, value);
        }

        for (field, value) in [
            (CallContextFieldTag::LastCalleeId, call.call_id.into()),
            (CallContextFieldTag::LastCalleeReturnDataOffset, 0.into()),
            (CallContextFieldTag::LastCalleeReturnDataLength, 0.into()),
        ] {
            self.call_context_write(exec_step, caller.call_id, field, value);
        }

        Ok(())
    }
}
