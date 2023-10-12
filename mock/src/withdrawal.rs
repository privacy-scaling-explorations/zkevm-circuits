//! Mock Withdrawal definition and builder related methods.

use eth_types::{geth_types::Withdrawal, Address};

#[derive(Debug, Clone)]
/// Mock structure which represents a Withdrawal and can be used for tests.
/// It contains all the builder-pattern methods required to be able to specify
/// any of it's details.
pub struct MockWithdrawal {
    pub id: u64,
    pub validator_id: u64,
    pub address: Address,
    pub amount: u64,
}

impl Default for MockWithdrawal {
    fn default() -> Self {
        MockWithdrawal {
            id: 0,
            validator_id: 0,
            address: Address::zero(),
            amount: 0,
        }
    }
}

impl From<MockWithdrawal> for ethers_core::types::Withdrawal {
    fn from(mock: MockWithdrawal) -> Self {
        ethers_core::types::Withdrawal {
            index: mock.id.into(),
            validator_index: mock.validator_id.into(),
            address: mock.address,
            amount: mock.amount.into(),
        }
    }
}

impl From<MockWithdrawal> for Withdrawal {
    fn from(mock: MockWithdrawal) -> Self {
        Withdrawal {
            id: mock.id,
            validator_id: mock.validator_id,
            address: mock.address,
            amount: mock.amount,
        }
    }
}

impl MockWithdrawal {
    /// Set id field for the MockWithdrawal.
    pub fn id(&mut self, id: u64) -> &mut Self {
        self.id = id;
        self
    }

    /// Set validator_id field for the MockWithdrawal.
    pub fn validator_id(&mut self, vid: u64) -> &mut Self {
        self.validator_id = vid;
        self
    }

    /// Set address field for the MockWithdrawal.
    pub fn address(&mut self, address: Address) -> &mut Self {
        self.address = address;
        self
    }

    /// Set amount field for the MockWithdrawal.
    pub fn amount(&mut self, amount: u64) -> &mut Self {
        self.amount = amount;
        self
    }
}
