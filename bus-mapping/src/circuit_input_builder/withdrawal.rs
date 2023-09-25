//! Withdrawal & WithdrawalContext utility module.

use eth_types::Address;

use crate::Error;

/// Context of a [`Withdrawal`].
#[derive(Debug, Default)]
pub struct WithdrawalContext {
    /// Unique identifier of a withdrawal. This value starts from 0 and then increases
    /// monotonically.
    id: u64,
}

impl WithdrawalContext {
    /// Return id of this withdrawal.
    pub fn id(&self) -> u64 {
        self.id
    }
}
/// Result of the parsing of an Ethereum Withdrawal.
#[derive(Debug, Copy, Clone, Default)]
pub struct Withdrawal {
    /// Unique identifier of a withdrawal in the whole history of withdrawals.
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
        self.amount * (10 ^ 9)
    }

    /// Constructor for padding withdrawal in withdrawal circuit
    pub fn padding_withdrawal(id: usize) -> Self {
        Self {
            id: id as u64,
            ..Default::default()
        }
    }
}
