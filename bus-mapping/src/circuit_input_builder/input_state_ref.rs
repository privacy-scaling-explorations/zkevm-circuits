//! CircuitInput builder tooling module.

use super::{
    get_call_memory_offset_length, get_create_init_code, Block, BlockContext, Call, CallContext,
    CallKind, CodeSource, CopyEvent, ExecState, ExecStep, ExpEvent, Transaction,
    TransactionContext,
};
use crate::{
    error::{DepthError, ExecError, InsufficientBalanceError, NonceUintOverflowError},
    exec_trace::OperationRef,
    operation::{
        AccountField, AccountOp, CallContextField, CallContextOp, MemoryOp, Op, OpEnum, Operation,
        StackOp, Target, TxAccessListAccountOp, TxLogField, TxLogOp, TxReceiptField, TxReceiptOp,
        RW,
    },
    precompile::{is_precompiled, PrecompileCalls},
    state_db::{CodeDB, StateDB},
    Error,
};
use eth_types::{
    evm_types::{
        gas_utils::memory_expansion_gas_cost, GasCost, MemoryAddress, OpcodeId, StackAddress,
    },
    Address, Bytecode, GethExecStep, ToAddress, ToBigEndian, ToWord, Word, H256, U256,
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
    /// Max rw number limit
    pub max_rws: Option<usize>,
}

impl<'a> CircuitInputStateRef<'a> {
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
            gas_left: self.tx.gas(),
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
                let mut gas_left = prev_step.gas_left - prev_step.gas_cost;

                // for contract creation
                let call = self.tx.calls()[0].clone();
                if call.is_create() {
                    let code_hash = self.sdb.get_account(&call.address).1.code_hash;
                    let bytecode_len = self.code(code_hash).unwrap().len() as u64;
                    let deposit_cost = bytecode_len * GasCost::CODE_DEPOSIT_BYTE_COST;
                    assert!(
                        gas_left >= deposit_cost,
                        "gas left {gas_left} is not enough for deposit cost {deposit_cost}"
                    );
                    gas_left -= deposit_cost;
                }

                gas_left
            } else {
                // consume all remaining gas when non revert err happens
                0
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

    /// Push an [`Operation`](crate::operation::Operation) into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter) and then adds a
    /// reference to the stored operation ([`OperationRef`]) inside the
    /// bus-mapping instance of the current [`ExecStep`].  Then increase the
    /// block_ctx [`RWCounter`](crate::operation::RWCounter) by one.
    pub fn push_op<T: Op>(&mut self, step: &mut ExecStep, rw: RW, op: T) -> Result<(), Error> {
        if let OpEnum::Account(op) = op.clone().into_enum() {
            self.check_update_sdb_account(rw, &op)
        }
        let op_ref =
            self.block
                .container
                .insert(Operation::new(self.block_ctx.rwc.inc_pre(), rw, op));
        step.bus_mapping_instance.push(op_ref);
        self.check_rw_num_limit()
    }

    /// Check whether rws will overflow circuit limit.
    pub fn check_rw_num_limit(&self) -> Result<(), Error> {
        if let Some(max_rws) = self.max_rws {
            let rwc = self.block_ctx.rwc.0;
            if rwc > max_rws {
                log::error!("rwc > max_rws, rwc={}, max_rws={}", rwc, max_rws);
                return Err(Error::RwsNotEnough(max_rws, rwc));
            };
        }

        Ok(())
    }

    /// Push a read type [`CallContextOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with
    /// the next [`RWCounter`](crate::operation::RWCounter)  and then adds a
    /// reference to the stored operation ([`OperationRef`]) inside the
    /// bus-mapping instance of the current [`ExecStep`].  Then increase the
    /// block_ctx [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn call_context_read(
        &mut self,
        step: &mut ExecStep,
        call_id: usize,
        field: CallContextField,
        value: Word,
    ) -> Result<(), Error> {
        let op = CallContextOp {
            call_id,
            field,
            value,
        };

        self.push_op(step, RW::READ, op)
    }

    /// Push a write type [`CallContextOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with
    /// the next [`RWCounter`](crate::operation::RWCounter)  and then adds a
    /// reference to the stored operation ([`OperationRef`]) inside the
    /// bus-mapping instance of the current [`ExecStep`].  Then increase the
    /// block_ctx [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn call_context_write(
        &mut self,
        step: &mut ExecStep,
        call_id: usize,
        field: CallContextField,
        value: Word,
    ) -> Result<(), Error> {
        let op = CallContextOp {
            call_id,
            field,
            value,
        };

        self.push_op(step, RW::WRITE, op)
    }

    /// Push an [`Operation`](crate::operation::Operation) with reversible to be
    /// true into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter) and then adds a
    /// reference to the stored operation
    /// ([`OperationRef`]) inside the
    /// bus-mapping instance of the current [`ExecStep`]. Then increase the
    /// block_ctx [`RWCounter`](crate::operation::RWCounter) by one.
    /// This method should be used in `Opcode::gen_associated_ops` instead of
    /// `push_op` when the operation is `RW::WRITE` and it can be reverted (for
    /// example, a write [`StorageOp`](crate::operation::StorageOp)).
    pub fn push_op_reversible<T: Op>(&mut self, step: &mut ExecStep, op: T) -> Result<(), Error> {
        self.check_apply_op(&op.clone().into_enum());
        let op_ref = self.block.container.insert(Operation::new_reversible(
            self.block_ctx.rwc.inc_pre(),
            RW::WRITE,
            op,
        ));
        step.bus_mapping_instance.push(op_ref);

        // Increase reversible_write_counter
        self.call_ctx_mut()?.reversible_write_counter += 1;
        step.reversible_write_counter_delta += 1;

        // Add the operation into reversible_ops if this call is not persistent
        if !self.call()?.is_persistent {
            self.tx_ctx
                .reversion_groups
                .last_mut()
                .expect("reversion_groups should not be empty for non-persistent call")
                .op_refs
                .push((self.tx.steps().len(), op_ref));
        }

        self.check_rw_num_limit()
    }

    /// Push a read type [`MemoryOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter) and `call_id`, and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter) by one.
    pub fn memory_read(
        &mut self,
        step: &mut ExecStep,
        address: MemoryAddress,
        _value: u8,
    ) -> Result<u8, Error> {
        let byte = &self.call_ctx()?.memory.read_chunk(address, 1.into())[0];
        let call_id = self.call()?.call_id;
        self.push_op(step, RW::READ, MemoryOp::new(call_id, address, *byte));
        Ok(*byte)
    }

    /// Push a read type [`MemoryOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter) and `caller_id`, and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn memory_read_caller(
        &mut self,
        step: &mut ExecStep,
        address: MemoryAddress, // Caution: make sure this address = slot passing
    ) -> Result<u8, Error> {
        let byte = &self.caller_ctx()?.memory.read_chunk(address, 1.into())[0];
        let call_id = self.call()?.caller_id;
        self.push_op(step, RW::READ, MemoryOp::new(call_id, address, *byte));
        Ok(*byte)
    }

    /// Push a write type [`MemoryOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter) and `call_id`, and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn memory_write(
        &mut self,
        step: &mut ExecStep,
        address: MemoryAddress,
        value: u8,
    ) -> Result<u8, Error> {
        let call_id = self.call()?.call_id;

        let mem = &mut self.call_ctx_mut()?.memory;
        let value_prev = mem.read_chunk(address, 1.into())[0];
        mem.write_chunk(address, &[value]);

        self.push_op(step, RW::WRITE, MemoryOp::new(call_id, address, value));
        Ok(value_prev)
    }

    /// Push a write type [`MemoryOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter) and `caller_id`, and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn memory_write_caller(
        &mut self,
        step: &mut ExecStep,
        address: MemoryAddress, // Caution: make sure this address = slot passing
        value: u8,
    ) -> Result<u8, Error> {
        let call_id = self.call()?.caller_id;

        let mem = &mut self.caller_ctx_mut()?.memory;
        let value_prev = mem.read_chunk(address, 1.into())[0];
        mem.write_chunk(address, &[value_prev]);

        self.push_op(step, RW::WRITE, MemoryOp::new(call_id, address, value));
        Ok(value_prev)
    }

    /// Push a write type [`StackOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter)  and `call_id`, and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter) by one.
    pub fn stack_write(
        &mut self,
        step: &mut ExecStep,
        address: StackAddress,
        value: Word,
    ) -> Result<(), Error> {
        let call_id = self.call()?.call_id;
        self.push_op(step, RW::WRITE, StackOp::new(call_id, address, value))?;
        Ok(())
    }

    /// Push a read type [`StackOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter)  and `call_id`, and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn stack_read(
        &mut self,
        step: &mut ExecStep,
        address: StackAddress,
        value: Word,
    ) -> Result<(), Error> {
        let call_id = self.call()?.call_id;
        self.push_op(step, RW::READ, StackOp::new(call_id, address, value))?;
        Ok(())
    }

    /// First check the validity and consistency of the rw operation against the
    /// account in the StateDB, then if the rw operation is a write, apply
    /// it to the corresponding account in the StateDB.
    fn check_update_sdb_account(&mut self, rw: RW, op: &AccountOp) {
        let account = self.sdb.get_account_mut(&op.address).1;
        // -- sanity check begin --
        // Verify that a READ doesn't change the field value
        if matches!(rw, RW::READ) && op.value_prev != op.value {
            panic!(
                "RWTable Account field read where value_prev != value rwc: {}, op: {:?}",
                self.block_ctx.rwc.0, op
            )
        }
        // NOTE: In the State Circuit we use code_hash=0 to encode non-existing
        // accounts, but the corresponding account in the state DB is empty
        // (which means code_hash=EMPTY_HASH).
        let account_value_prev = match op.field {
            AccountField::Nonce => account.nonce.to_word(),
            AccountField::Balance => account.balance,
            AccountField::CodeHash => {
                if account.is_empty() {
                    if op.value.is_zero() {
                        // Writing code_hash=0 to empty account is a noop to the StateDB.
                        return;
                    }
                    // Reading a code_hash=EMPTY_HASH of an empty account in the StateDB is encoded
                    // as code_hash=0 (non-existing account encoding) in the State Circuit.
                    Word::zero()
                } else {
                    account.code_hash.to_word()
                }
            }
        };

        // Verify that the previous value matches the account field value in the StateDB
        if op.value_prev != account_value_prev {
            panic!(
                "RWTable Account field {:?} lookup doesn't match account value
        account: {:?}, rwc: {}, op: {:?}",
                rw, account, self.block_ctx.rwc.0, op
            );
        }
        // Verify that no read is done to a field other than CodeHash to a non-existing
        // account (only CodeHash reads with value=0 can be done to non-existing
        // accounts, which the State Circuit translates to MPT
        // AccountNonExisting proofs lookups).
        if (!matches!(op.field, AccountField::CodeHash)
            && (matches!(rw, RW::READ) || (op.value_prev.is_zero() && op.value.is_zero())))
            && account.is_empty()
        {
            panic!(
                "RWTable Account field {:?} lookup to non-existing account rwc: {}, op: {:?}",
                rw, self.block_ctx.rwc.0, op
            );
        }
        // -- sanity check end --
        // Perform the write to the account in the StateDB
        if matches!(rw, RW::WRITE) {
            match op.field {
                AccountField::Nonce => account.nonce = op.value.as_u64(),
                AccountField::Balance => account.balance = op.value,
                AccountField::CodeHash => account.code_hash = H256::from(op.value.to_be_bytes()),
            }
        }
    }

    /// Push a read type [`AccountOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter), and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn account_read(
        &mut self,
        step: &mut ExecStep,
        address: Address,
        field: AccountField,
        value: Word,
    ) -> Result<(), Error> {
        let op = AccountOp::new(address, field, value, value);
        self.push_op(step, RW::READ, op)
    }

    /// Push a write type [`AccountOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter), and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn account_write(
        &mut self,
        step: &mut ExecStep,
        address: Address,
        field: AccountField,
        value: Word,
        value_prev: Word,
        reversible: bool,
    ) -> Result<(), Error> {
        let op = AccountOp::new(address, field, value, value_prev);
        if reversible {
            self.push_op_reversible(step, op)?;
        } else {
            self.push_op(step, RW::WRITE, op)?;
        }
        Ok(())
    }

    /// Push a write type [`TxLogOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter), and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn tx_log_write(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        log_id: usize,
        field: TxLogField,
        index: usize,
        value: Word,
    ) -> Result<(), Error> {
        self.push_op(
            step,
            RW::WRITE,
            TxLogOp::new(tx_id, log_id, field, index, value),
        )
    }

    /// Push a read type [`TxReceiptOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter), and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn tx_receipt_read(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        field: TxReceiptField,
        value: u64,
    ) -> Result<(), Error> {
        self.push_op(
            step,
            RW::READ,
            TxReceiptOp {
                tx_id,
                field,
                value,
            },
        )
    }

    /// Push a write type [`TxReceiptOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter), and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn tx_receipt_write(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        field: TxReceiptField,
        value: u64,
    ) -> Result<(), Error> {
        self.push_op(
            step,
            RW::WRITE,
            TxReceiptOp {
                tx_id,
                field,
                value,
            },
        )
    }

    /// Push a write type [`TxAccessListAccountOp`] into the
    /// [`OperationContainer`](crate::operation::OperationContainer) with the
    /// next [`RWCounter`](crate::operation::RWCounter), and then
    /// adds a reference to the stored operation ([`OperationRef`]) inside
    /// the bus-mapping instance of the current [`ExecStep`].  Then increase
    /// the `block_ctx` [`RWCounter`](crate::operation::RWCounter)  by one.
    pub fn tx_accesslist_account_write(
        &mut self,
        step: &mut ExecStep,
        tx_id: usize,
        address: Address,
        is_warm: bool,
        is_warm_prev: bool,
    ) -> Result<(), Error> {
        self.push_op(
            step,
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id,
                address,
                is_warm,
                is_warm_prev,
            },
        )
    }

    /// Add address to access list for the current transaction.
    pub fn tx_access_list_write(
        &mut self,
        step: &mut ExecStep,
        address: Address,
    ) -> Result<(), Error> {
        let is_warm = self.sdb.check_account_in_access_list(&address);
        self.push_op_reversible(
            step,
            TxAccessListAccountOp {
                tx_id: self.tx_ctx.id(),
                address,
                is_warm: true,
                is_warm_prev: is_warm,
            },
        )
    }

    /// Push 2 reversible [`AccountOp`] to update `sender` and `receiver`'s
    /// balance by `value`. If `fee` is existing (not None), also need to push 1
    /// non-reversible [`AccountOp`] to update `sender` balance by `fee`.
    #[allow(clippy::too_many_arguments)]
    pub fn transfer_with_fee(
        &mut self,
        step: &mut ExecStep,
        sender: Address,
        receiver: Address,
        receiver_exists: bool,
        must_create: bool,
        value: Word,
        fee: Option<Word>,
    ) -> Result<(), Error> {
        let (found, sender_account) = self.sdb.get_account(&sender);
        if !found {
            return Err(Error::AccountNotFound(sender));
        }
        let mut sender_balance_prev = sender_account.balance;
        debug_assert!(
            sender_account.balance >= value + fee.unwrap_or_default(),
            "invalid amount balance {:?} value {:?} fee {:?}",
            sender_balance_prev,
            value,
            fee
        );
        if let Some(fee) = fee {
            let sender_balance = sender_balance_prev - fee;
            log::trace!(
                "sender balance update with fee (not reversible): {:?} {:?}->{:?}",
                sender,
                sender_balance_prev,
                sender_balance
            );
            self.push_op(
                step,
                RW::WRITE,
                AccountOp {
                    address: sender,
                    field: AccountField::Balance,
                    value: sender_balance,
                    value_prev: sender_balance_prev,
                },
            )?;
            sender_balance_prev = sender_balance;
        }
        let sender_balance = sender_balance_prev - value;
        log::trace!(
            "sender balance update with value: {:?} {:?}->{:?}",
            sender,
            sender_balance_prev,
            sender_balance
        );
        // If receiver doesn't exist, create it
        if !receiver_exists && (!value.is_zero() || must_create) {
            self.push_op_reversible(
                step,
                AccountOp {
                    address: receiver,
                    field: AccountField::CodeHash,
                    value: CodeDB::empty_code_hash().to_word(),
                    value_prev: Word::zero(),
                },
            )?;
        }
        if value.is_zero() {
            // Skip transfer if value == 0
            return Ok(());
        }

        self.push_op_reversible(
            step,
            AccountOp {
                address: sender,
                field: AccountField::Balance,
                value: sender_balance,
                value_prev: sender_balance_prev,
            },
        )?;

        let (_found, receiver_account) = self.sdb.get_account(&receiver);
        let receiver_balance_prev = receiver_account.balance;
        let receiver_balance = receiver_account.balance + value;
        self.push_op_reversible(
            step,
            AccountOp {
                address: receiver,
                field: AccountField::Balance,
                value: receiver_balance,
                value_prev: receiver_balance_prev,
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
        receiver_exists: bool,
        must_create: bool,
        value: Word,
    ) -> Result<(), Error> {
        self.transfer_with_fee(
            step,
            sender,
            receiver,
            receiver_exists,
            must_create,
            value,
            None,
        )
    }

    /// Transfer to an address. Create an account if it is not existed before.
    pub fn transfer_to(
        &mut self,
        step: &mut ExecStep,
        receiver: Address,
        receiver_exists: bool,
        must_create: bool,
        value: Word,
        reversible: bool,
    ) -> Result<(), Error> {
        // If receiver doesn't exist, create it
        if (!receiver_exists && !value.is_zero()) || must_create {
            self.account_write(
                step,
                receiver,
                AccountField::CodeHash,
                CodeDB::empty_code_hash().to_word(),
                Word::zero(),
                reversible,
            )?;
        }
        if value.is_zero() {
            // Skip transfer if value == 0
            return Ok(());
        }
        let (_found, receiver_account) = self.sdb.get_account(&receiver);
        let receiver_balance_prev = receiver_account.balance;
        let receiver_balance = receiver_account.balance + value;
        self.account_write(
            step,
            receiver,
            AccountField::Balance,
            receiver_balance,
            receiver_balance_prev,
            reversible,
        )?;

        Ok(())
    }

    /// Fetch and return code for the given code hash from the code DB.
    pub fn code(&self, code_hash: H256) -> Result<Vec<u8>, Error> {
        self.code_db
            .get_from_h256(&code_hash)
            .map(|bytecode| bytecode.code())
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
            salt.to_be_bytes(),
            init_code,
        ))
    }

    /// read reversion info
    pub(crate) fn reversion_info_read(
        &mut self,
        step: &mut ExecStep,
        call: &Call,
    ) -> Result<(), Error> {
        for (field, value) in [
            (
                CallContextField::RwCounterEndOfReversion,
                call.rw_counter_end_of_reversion.to_word(),
            ),
            (CallContextField::IsPersistent, call.is_persistent.to_word()),
        ] {
            self.call_context_read(step, call.call_id, field, value)?;
        }
        Ok(())
    }

    /// write reversion info
    pub(crate) fn reversion_info_write(
        &mut self,
        step: &mut ExecStep,
        call: &Call,
    ) -> Result<(), Error> {
        for (field, value) in [
            (
                CallContextField::RwCounterEndOfReversion,
                call.rw_counter_end_of_reversion.to_word(),
            ),
            (CallContextField::IsPersistent, call.is_persistent.to_word()),
        ] {
            self.call_context_write(step, call.call_id, field, value)?;
        }
        Ok(())
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
            call_id: self.block_ctx.rwc.0,
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
    fn get_rev_op_by_ref(&self, op_ref: &OperationRef) -> Option<OpEnum> {
        match op_ref {
            OperationRef(Target::Storage, idx) => {
                let operation = &self.block.container.storage[*idx];
                if operation.rw().is_write() && operation.reversible() {
                    Some(OpEnum::Storage(operation.op().reverse()))
                } else {
                    None
                }
            }
            OperationRef(Target::TxAccessListAccount, idx) => {
                let operation = &self.block.container.tx_access_list_account[*idx];
                if operation.rw().is_write() && operation.reversible() {
                    Some(OpEnum::TxAccessListAccount(operation.op().reverse()))
                } else {
                    None
                }
            }
            OperationRef(Target::TxAccessListAccountStorage, idx) => {
                let operation = &self.block.container.tx_access_list_account_storage[*idx];
                if operation.rw().is_write() && operation.reversible() {
                    Some(OpEnum::TxAccessListAccountStorage(operation.op().reverse()))
                } else {
                    None
                }
            }
            OperationRef(Target::TxRefund, idx) => {
                let operation = &self.block.container.tx_refund[*idx];
                if operation.rw().is_write() && operation.reversible() {
                    Some(OpEnum::TxRefund(operation.op().reverse()))
                } else {
                    None
                }
            }
            OperationRef(Target::Account, idx) => {
                let operation = &self.block.container.account[*idx];
                if operation.rw().is_write() && operation.reversible() {
                    Some(OpEnum::Account(operation.op().reverse()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Check and apply op to state.
    fn check_apply_op(&mut self, op: &OpEnum) {
        match &op {
            OpEnum::Storage(op) => {
                self.sdb.set_storage(&op.address, &op.key, &op.value);
            }
            OpEnum::TxAccessListAccount(op) => {
                if !op.is_warm_prev && op.is_warm {
                    self.sdb.add_account_to_access_list(op.address);
                }
                if op.is_warm_prev && !op.is_warm {
                    self.sdb.remove_account_from_access_list(&op.address);
                }
            }
            OpEnum::TxAccessListAccountStorage(op) => {
                if !op.is_warm_prev && op.is_warm {
                    self.sdb
                        .add_account_storage_to_access_list((op.address, op.key));
                }
                if op.is_warm_prev && !op.is_warm {
                    self.sdb
                        .remove_account_storage_from_access_list(&(op.address, op.key));
                }
            }
            OpEnum::Account(op) => self.check_update_sdb_account(RW::WRITE, op),
            OpEnum::TxRefund(op) => {
                self.sdb.set_refund(op.value);
            }
            _ => unreachable!(),
        };
    }

    /// Handle a reversion group
    pub fn handle_reversion(&mut self, current_exec_steps: &mut [&mut ExecStep]) {
        // We already know that the call has reverted. Only the precompile failure case must be
        // handled differently as the ExecSteps associated with those calls haven't yet been pushed
        // to the tx's steps.

        let reversion_group = self
            .tx_ctx
            .reversion_groups
            .pop()
            .expect("reversion_groups should not be empty for non-persistent call");

        // Apply reversions
        for (step_index, op_ref) in reversion_group.op_refs.iter().rev().copied() {
            if let Some(op) = self.get_rev_op_by_ref(&op_ref) {
                self.check_apply_op(&op);
                let rev_op_ref = self.block.container.insert_op_enum(
                    self.block_ctx.rwc.inc_pre(),
                    RW::WRITE,
                    false,
                    op,
                );

                let step: &mut ExecStep = if step_index >= self.tx.steps_mut().len() {
                    // the `current_exec_steps` will be appended after self.tx.steps
                    // So here we do an index-mapping
                    current_exec_steps[step_index - self.tx.steps_mut().len()]
                } else {
                    &mut self.tx.steps_mut()[step_index]
                };
                step.bus_mapping_instance.push(rev_op_ref);
            }
        }

        // Set calls' `rw_counter_end_of_reversion`
        let rwc = self.block_ctx.rwc.0 - 1;
        for (call_idx, reversible_write_counter_offset) in reversion_group.calls {
            self.tx.calls_mut()[call_idx].rw_counter_end_of_reversion =
                rwc - reversible_write_counter_offset;
        }
    }

    /// Handle a restore and a return step caused by any opcode that causes a return to the
    /// previous call context.
    pub fn handle_return(
        &mut self,
        current_exec_steps: &mut [&mut ExecStep],
        // exec_step: &mut ExecStep,
        geth_steps: &[GethExecStep],
        need_restore: bool,
    ) -> Result<(), Error> {
        let step = &geth_steps[0];

        // For these 6 opcodes, the return data should be handled in opcodes respectively.
        // For other opcodes/states, return data must be empty.
        if !matches!(
            step.op,
            OpcodeId::RETURN
                | OpcodeId::REVERT
                | OpcodeId::CALL
                | OpcodeId::CALLCODE
                | OpcodeId::DELEGATECALL
                | OpcodeId::STATICCALL
        ) || current_exec_steps[0].error.is_some()
        {
            if let Ok(caller) = self.caller_ctx_mut() {
                caller.return_data.clear();
            }
        }
        if need_restore {
            // only precompile needs more than 1 current_exec_steps
            if current_exec_steps.len() > 1 {
                debug_assert!(
                    current_exec_steps[1].is_precompiled()
                        || current_exec_steps[1].is_precompile_oog_err()
                );
            }

            self.handle_restore_context(
                current_exec_steps[current_exec_steps.len() - 1],
                geth_steps,
            )?;
        }

        // handle return_data
        let (return_data_offset, return_data_length) = {
            if !self.call()?.is_root {
                let (offset, length) = match step.op {
                    OpcodeId::RETURN | OpcodeId::REVERT => {
                        let (offset, length) = if step.error.is_some()
                            || (self.call()?.is_create() && self.call()?.is_success)
                        {
                            (0, 0)
                        } else {
                            (
                                step.stack.nth_last(0)?.as_usize(),
                                step.stack.nth_last(1)?.as_usize(),
                            )
                        };

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
                    OpcodeId::CALL | OpcodeId::CALLCODE | OpcodeId::DELEGATECALL | OpcodeId::STATICCALL => {
                        if self.call()?.is_success {
                            let callee_memory = self.call_ctx()?.memory.clone();
                            let caller_ctx = self.caller_ctx_mut()?;

                            let return_data_offset = caller_ctx.memory.len() - callee_memory.len();
                            let return_data_length = callee_memory.len();

                            caller_ctx.memory.copy_from(
                                (return_data_offset).into(), 
                                0.into(), 
                                return_data_length.into(), 
                                &callee_memory.0
                            );
                            (return_data_offset, return_data_length)
                        } else {
                            (0, 0)
                        }
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
        let call_success_create: bool =
            call.is_create() && call.is_success && step.op == OpcodeId::RETURN;

        // Store deployed code if it's a successful create
        if call_success_create {
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
            self.handle_reversion(current_exec_steps);
        }

        // If current call has caller.
        if let Ok(caller) = self.caller_mut() {
            caller.last_callee_id = call.call_id;
            // EIP-211 CREATE/CREATE2 call successful case should set RETURNDATASIZE = 0
            if call_success_create {
                caller.last_callee_return_data_length = 0u64;
                caller.last_callee_return_data_offset = 0u64;
            } else {
                caller.last_callee_return_data_length = return_data_length;
                caller.last_callee_return_data_offset = return_data_offset;
            }
        }

        // If current call has caller_ctx (has caller)
        if let Ok(caller_ctx) = self.caller_ctx_mut() {
            // EIP-211 CREATE/CREATE2 call successful case should set RETURNDATASIZE = 0
            if call_success_create {
                caller_ctx.return_data.truncate(0);
            }
        }

        self.tx_ctx.pop_call_ctx();

        Ok(())
    }

    // The returned (return_data_offset, return_data_len) pair, is the values used to calculate
    // memory expansion cost when successful case. So for "successful deployment" case, it will
    // be non 0 while the call_ctx.return should be empty for this case. EIP-211: CREATE/CREATE2
    // call successful case should set RETURNDATASIZE = 0
    fn get_return_data_offset_and_len(
        exec_step: &ExecStep,
        geth_step: &GethExecStep,
        caller_ctx: &CallContext,
    ) -> Result<(U256, U256), Error> {
        let is_err = exec_step.error.is_some();
        let [last_callee_return_data_offset, last_callee_return_data_length] = if is_err {
            [Word::zero(), Word::zero()]
        } else {
            match geth_step.op {
                OpcodeId::STOP => [Word::zero(); 2],
                OpcodeId::CALL
                | OpcodeId::CALLCODE
                | OpcodeId::STATICCALL
                | OpcodeId::DELEGATECALL => {
                    let return_data_length = match exec_step.exec_state {
                        ExecState::Precompile(_) => {
                            // successful precompile call
                            caller_ctx.return_data.len().into()
                        }
                        _ => Word::zero(),
                    };
                    [Word::zero(), return_data_length]
                }
                OpcodeId::REVERT | OpcodeId::RETURN => {
                    let offset = geth_step.stack.nth_last(0)?;
                    let length = geth_step.stack.nth_last(1)?;
                    // This is the convention we are using for memory addresses so that there is no
                    // memory expansion cost when the length is 0.
                    // https://github.com/privacy-scaling-explorations/zkevm-circuits/pull/279/files#r787806678
                    if length.is_zero() {
                        [Word::zero(); 2]
                    } else {
                        [offset, length]
                    }
                }
                _ => [Word::zero(), Word::zero()],
            }
        };
        Ok((
            last_callee_return_data_offset,
            last_callee_return_data_length,
        ))
    }

    /// Bus mapping for the RestoreContextGadget as used in RETURN.
    pub fn handle_restore_context(
        &mut self,
        exec_step: &mut ExecStep,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let call = self.call()?.clone();
        let geth_step = steps
            .get(0)
            .ok_or(Error::InternalError("invalid index 0"))?;
        let is_err = exec_step.error.is_some();
        let is_revert_or_return_call_success = (geth_step.op == OpcodeId::REVERT
            || geth_step.op == OpcodeId::RETURN)
            && exec_step.error.is_none();

        if !is_revert_or_return_call_success
            && !call.is_success
            && !exec_step.is_precompiled()
            && !exec_step.is_precompile_oog_err()
        {
            // add call failure ops for exception cases
            self.call_context_read(
                exec_step,
                call.call_id,
                CallContextField::IsSuccess,
                0u64.into(),
            )?;

            // Even call.rw_counter_end_of_reversion is zero for now, it will set in
            // set_value_ops_call_context_rwc_eor later
            // if call fails, no matter root or internal, read RwCounterEndOfReversion for
            // circuit constraint.
            self.call_context_read(
                exec_step,
                call.call_id,
                CallContextField::RwCounterEndOfReversion,
                call.rw_counter_end_of_reversion.into(),
            )?;

            if call.is_root {
                return Ok(());
            }
        }

        let caller = self.caller()?.clone();
        let geth_step_next = steps
            .get(1)
            .ok_or(Error::InternalError("invalid index 1"))?;
        self.call_context_read(
            exec_step,
            call.call_id,
            CallContextField::CallerId,
            caller.call_id.into(),
        )?;

        let [last_callee_return_data_offset, last_callee_return_data_length] =
            if exec_step.error.is_some() {
                [Word::zero(); 2]
            } else {
                match geth_step.op {
                    OpcodeId::STOP => [Word::zero(); 2],
                    OpcodeId::REVERT | OpcodeId::RETURN => {
                        let offset = geth_step.stack.nth_last(0)?;
                        let length = geth_step.stack.nth_last(1)?;
                        // This is the convention we are using for memory addresses so that there is
                        // no memory expansion cost when the length is 0.
                        if length.is_zero() {
                            [Word::zero(); 2]
                        } else {
                            [offset, length]
                        }
                    }
                    _ => [Word::zero(), Word::zero()],
                }
            };
        let gas_refund = if exec_step.error.is_some() {
            0
        } else if exec_step.is_precompiled() {
            exec_step.gas_left - exec_step.gas_cost
        } else {
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
                GasCost::CODE_DEPOSIT_BYTE_COST * last_callee_return_data_length.as_u64()
            } else {
                0
            };
            let constant_step_gas = match geth_step.op {
                OpcodeId::SELFDESTRUCT => geth_step.gas_cost,
                _ => 0, // RETURN/STOP/REVERT have no "constant_step_gas"
            };
            geth_step.gas - memory_expansion_gas_cost - code_deposit_cost - constant_step_gas
        };

        let caller_gas_left = geth_step_next.gas.checked_sub(gas_refund).unwrap_or_else (
            || {
                panic!("caller_gas_left underflow geth_step_next {geth_step_next:?}, gas_refund {gas_refund:?}, exec_step {exec_step:?}, geth_step {geth_step:?}");
            }
        );

        for (field, value) in [
            (CallContextField::IsRoot, (caller.is_root as u64).into()),
            (
                CallContextField::IsCreate,
                (caller.is_create() as u64).into(),
            ),
            (CallContextField::CodeHash, caller.code_hash.to_word()),
            (CallContextField::ProgramCounter, geth_step_next.pc.into()),
            (
                CallContextField::StackPointer,
                geth_step_next.stack.stack_pointer().0.into(),
            ),
            (CallContextField::GasLeft, caller_gas_left.into()),
            (
                CallContextField::MemorySize,
                self.caller_ctx()?.memory.word_size().into(),
            ),
            (
                CallContextField::ReversibleWriteCounter,
                self.caller_ctx()?.reversible_write_counter.into(),
            ),
        ] {
            self.call_context_read(exec_step, caller.call_id, field, value)?;
        }

        // EIP-211: CREATE/CREATE2 call successful case should set RETURNDATASIZE = 0
        let discard_return_data =
            call.is_create() && geth_step.op == OpcodeId::RETURN || exec_step.error.is_some();
        for (field, value) in [
            (CallContextField::LastCalleeId, call.call_id.into()),
            (
                CallContextField::LastCalleeReturnDataOffset,
                if discard_return_data {
                    U256::zero()
                } else {
                    last_callee_return_data_offset
                },
            ),
            (
                CallContextField::LastCalleeReturnDataLength,
                if discard_return_data {
                    U256::zero()
                } else {
                    last_callee_return_data_length
                },
            ),
        ] {
            self.call_context_write(exec_step, caller.call_id, field, value)?;
        }

        Ok(())
    }

    /// Push a copy event to the state.
    pub fn push_copy(&mut self, step: &mut ExecStep, event: CopyEvent) {
        step.copy_rw_counter_delta += event.rw_counter_delta();
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
        if let Ok(error) = ExecError::try_from(step) {
            return Ok(Some(error));
        }

        if matches!(step.op, OpcodeId::INVALID(_)) {
            return Ok(Some(ExecError::InvalidOpcode));
        }

        let call = self.call()?;

        if matches!(next_step, None) {
            // enumerating call scope successful cases
            // case 1: call with normal halt opcode termination
            if matches!(
                step.op,
                OpcodeId::STOP | OpcodeId::REVERT | OpcodeId::SELFDESTRUCT
            ) {
                return Ok(None);
            }
            // case 2: call is NOT Create (Create represented by empty tx.to) and halt by
            // opcode::Return
            if !call.is_create() && step.op == OpcodeId::RETURN {
                return Ok(None);
            }
            // case 3 Create with successful RETURN
            if call.is_create() && call.is_success && step.op == OpcodeId::RETURN {
                return Ok(None);
            }
            // more other case...
        }

        let next_depth = next_step.map(|s| s.depth).unwrap_or(0);
        let next_result = next_step
            .map(|s| s.stack.last().unwrap_or_else(|_| Word::zero()))
            .unwrap_or_else(Word::zero);

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
                            Box::new(step.clone()),
                        ));
                    }
                });
            } else {
                // Return from a {CREATE, CREATE2} with a failure, via RETURN
                if call.is_create() {
                    let offset = step.stack.nth_last(0)?;
                    let length = step.stack.nth_last(1)?;
                    if length > Word::from(0x6000u64) {
                        return Ok(Some(ExecError::MaxCodeSizeExceeded));
                    } else if length > Word::zero()
                        && !call_ctx.memory.is_empty()
                        && call_ctx.memory.0.get(offset.low_u64() as usize) == Some(&0xef)
                    {
                        return Ok(Some(ExecError::InvalidCreationCode));
                    } else if Word::from(200u64) * length > Word::from(step.gas) {
                        return Ok(Some(ExecError::CodeStoreOutOfGas));
                    } else {
                        return Err(Error::UnexpectedExecStepError(
                            "failure in RETURN from {CREATE, CREATE2}",
                            Box::new(step.clone()),
                        ));
                    }
                } else {
                    return Err(Error::UnexpectedExecStepError(
                        "failure in RETURN",
                        Box::new(step.clone()),
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
                Box::new(step.clone()),
            ));
        }

        // The *CALL*/CREATE* code was not executed
        let next_pc = next_step.map(|s| s.pc).unwrap_or(1);
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
                return Ok(Some(ExecError::Depth(match step.op {
                    OpcodeId::CALL
                    | OpcodeId::CALLCODE
                    | OpcodeId::DELEGATECALL
                    | OpcodeId::STATICCALL => DepthError::Call,
                    OpcodeId::CREATE => DepthError::Create,
                    OpcodeId::CREATE2 => DepthError::Create2,
                    op => {
                        unreachable!("Depth error unexpected for opcode: {:?}", op)
                    }
                })));
            }

            let sender = self.call()?.address;
            let (found, account) = self.sdb.get_account(&sender);
            if !found {
                return Err(Error::AccountNotFound(sender));
            }
            if account.balance < value {
                return Ok(Some(ExecError::InsufficientBalance(match step.op {
                    OpcodeId::CALL | OpcodeId::CALLCODE => InsufficientBalanceError::Call,
                    OpcodeId::CREATE => InsufficientBalanceError::Create,
                    OpcodeId::CREATE2 => InsufficientBalanceError::Create2,
                    op => {
                        unreachable!("insufficient balance error unexpected for opcode: {:?}", op)
                    }
                })));
            }

            // Nonce Uint overflow
            // If user's nonce is equal u64::MAX, nonce will be overflow in this call
            // Nonce is u64 so it's impossible to larger than u64::MAX, that's why we're using `==`
            // here.
            if account.nonce == u64::MAX {
                return Ok(Some(ExecError::NonceUintOverflow(match step.op {
                    OpcodeId::CREATE => NonceUintOverflowError::Create,
                    OpcodeId::CREATE2 => NonceUintOverflowError::Create2,
                    op => unreachable!("Nonce Uint overflow error unexpected for opcode: {:?}", op),
                })));
            }

            // Address collision
            if matches!(step.op, OpcodeId::CREATE2) {
                let address = self.create2_address(step)?;

                let (found, _) = self.sdb.get_account(&address);
                if found {
                    return Ok(Some(ExecError::ContractAddressCollision));
                }
            }

            // Precompile call failures.
            if matches!(
                step.op,
                OpcodeId::CALL | OpcodeId::CALLCODE | OpcodeId::DELEGATECALL | OpcodeId::STATICCALL
            ) {
                let code_address = step.stack.nth_last(1)?.to_address();
                // NOTE: we do not know the amount of gas that precompile got here
                //   because the callGasTemp might probably be smaller than the gas
                //   on top of the stack (step.stack.last())
                // Therefore we postpone the oog handling to the implementor of callop.
                if is_precompiled(&code_address) {
                    let precompile_call: PrecompileCalls = code_address[19].into();
                    match precompile_call {
                        PrecompileCalls::Sha256
                        | PrecompileCalls::Ripemd160
                        | PrecompileCalls::Blake2F => {
                            // Log the precompile address and gas left. Since this failure is mainly
                            // caused by out of gas.
                            log::trace!(
                                "Precompile failed: code_address = {}, step.gas = {}",
                                code_address,
                                step.gas,
                            );
                            return Ok(Some(ExecError::PrecompileFailed));
                        }
                        pre_call => {
                            log::trace!(
                                "Precompile call failed: addr={:?}, step.gas={:?}",
                                pre_call,
                                step.gas
                            );
                            return Ok(None);
                        }
                    }
                }
            }

            return Err(Error::UnexpectedExecStepError(
                "*CALL*/CREATE* code not executed",
                Box::new(step.clone()),
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

    /// Generate copy steps for bytecode.
    pub(crate) fn gen_copy_steps_for_bytecode(
        &mut self,
        exec_step: &mut ExecStep,
        bytecode: &Bytecode,
        src_addr: u64,
        dst_addr: u64,
        src_addr_end: u64,
        bytes_left: u64,
    ) -> Result<Vec<(u8, bool)>, Error> {
        let mut copy_steps = Vec::with_capacity(bytes_left as usize);
        for idx in 0..bytes_left {
            let addr = src_addr.checked_add(idx).unwrap_or(src_addr_end);
            let step = bytecode.get(addr as usize).unwrap_or_default();
            copy_steps.push(step);
            self.memory_write(exec_step, (dst_addr + idx).into(), step.0)?;
        }

        Ok(copy_steps)
    }

    pub(crate) fn gen_copy_steps_for_precompile_calldata(
        &mut self,
        exec_step: &mut ExecStep,
        src_addr: u64,
        copy_length: u64,
    ) -> Result<Vec<u8>, Error> {
        let mut input_bytes: Vec<u8> = vec![];

        if copy_length != 0 {
            let start_byte_index = src_addr;
            for i in 0..copy_length {
                let b = self.memory_read_caller(exec_step, (start_byte_index + i).into())?;
                input_bytes.push(b);
            }
        }

        Ok(input_bytes)
    }

    pub(crate) fn gen_copy_steps_for_precompile_callee_memory(
        &mut self,
        exec_step: &mut ExecStep,
        result: &[u8],
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        if result.is_empty() {
            return Ok((vec![], vec![]));
        } else {
            let mut prev_bytes = vec![];
            let mut byte_index = 0;
            for byte in result {
                let prev_byte = self.memory_write(exec_step, byte_index.into(), *byte)?;
                prev_bytes.push(prev_byte);
                byte_index += 1;
            }

            Ok((result.into(), prev_bytes.into()))
        }
    }

    pub(crate) fn gen_copy_steps_for_precompile_returndata(
        &mut self,
        exec_step: &mut ExecStep,
        dst_addr: impl Into<MemoryAddress>,
        copy_length: impl Into<MemoryAddress>,
        result: &[u8],
    ) -> Result<Vec<u8>, Error> {
        let copy_length = copy_length.into().0;
        let mut return_bytes: Vec<u8> = vec![];

        if copy_length != 0 {
            assert!(copy_length <= result.len());

            let mut src_byte_index: usize = 0;
            let mut dst_byte_index: usize = dst_addr.into().0;

            for b in result.iter().take(copy_length) {
                self.memory_read(exec_step, src_byte_index.into(), 0)?;
                src_byte_index += 1;

                self.memory_write_caller(exec_step, dst_byte_index.into(), *b)?;
                dst_byte_index += 1;

                return_bytes.push(*b);
            }
        }

        Ok(return_bytes)
    }

    /// Generate copy steps for call data.
    pub(crate) fn gen_copy_steps_for_call_data(
        &mut self,
        exec_step: &mut ExecStep,
        src_addr: u64,
        dst_addr: u64,
        src_addr_end: u64,
        bytes_left: u64,
    ) -> Result<Vec<(u8, bool)>, Error> {
        let mut copy_steps = Vec::with_capacity(bytes_left as usize);
        for idx in 0..bytes_left {
            let addr = src_addr.checked_add(idx).unwrap_or(src_addr_end);
            let value = if addr < src_addr_end {
                let byte =
                    self.call_ctx()?.call_data[(addr - self.call()?.call_data_offset) as usize];
                if !self.call()?.is_root {
                    self.push_op(
                        exec_step,
                        RW::READ,
                        MemoryOp::new(self.call()?.caller_id, addr.into(), byte),
                    )?;
                }
                byte
            } else {
                0
            };
            copy_steps.push((value, false));
            self.memory_write(exec_step, (dst_addr + idx).into(), value)?;
        }

        Ok(copy_steps)
    }
}
