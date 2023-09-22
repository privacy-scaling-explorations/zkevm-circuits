//! Withdrawal & WithdrawalContext utility module.

use std::collections::BTreeMap;

use eth_types::{evm_types::Memory, geth_types, Address, GethExecTrace};
use ethers_core::utils::get_contract_address;

use crate::{
    state_db::{CodeDB, StateDB},
    Error,
};

use super::{call::ReversionGroup, Call, CallContext, CallKind, CodeSource, ExecStep};

#[derive(Debug, Default)]
/// Context of a [`Withdrawal`] which can mutate in an [`ExecStep`].
pub struct WithdrawalContext {
    /// Unique identifier of a withdrawal. This value starts from 0 and then increases
    /// monotonically.
    id: u64,

    /// Reversible Write Counter tracks the number of write operations in the
    /// call. It is incremented when a sub-call in this call succeeds by the
    /// number of successful writes in the sub-call.
    pub reversible_write_counter: usize,
}

impl WithdrawalContext {
    /// Return id of the this withdrawal.
    pub fn id(&self) -> u64 {
        self.id
    }
}

#[derive(Debug, Clone, Default)]
/// Result of the parsing of an Ethereum Withdrawal.
pub struct Withdrawal {
    /// Unique identifier of a withdrawal. This value starts from 0 and then increases
    /// monotonically.
    pub id: u64,
    /// Unique identifier of a validator.
    pub validator_id: u64,
    /// Address to be withdrawn to.
    pub address: Address,
    /// Withdrawal amount in Gwei.
    pub amount: u64,
}

impl Withdrawal {
    /// Create a new Self
    pub fn new(id: u64, validator_id: u64, address: Address, amount: u64) -> Result<Self, Error> {
        Ok(Self {
            id,
            validator_id,
            address,
            amount,
        })
    }
    /// Return the amount in this withdrawal
    pub fn amount_in_wei(&self) -> u64 {
        self.amount * 10 ^ 9
    }

    /// Constructor for padding withdrawal in withdrawal circuit
    pub fn padding_withdrawal(id: usize) -> Self {
        Self {
            id: id as u64,
            ..Default::default()
        }
    }
}
