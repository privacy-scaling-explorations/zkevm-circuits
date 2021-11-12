//! This module contains the logic for parsing and interacting with EVM
//! execution traces.
use crate::eth_types::Address;
use crate::eth_types::U64;
use crate::eth_types::{Block, Hash, Word};
use crate::operation::Target;
use serde::Serialize;
use std::str::FromStr;

/// Definition of all of the constants related to an Ethereum block and
/// chain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BlockConstants {
    hash: Hash, // Until we know how to deal with it
    coinbase: Address,
    timestamp: Word,
    number: U64, // u64
    difficulty: Word,
    gas_limit: Word,
    chain_id: Word,
    base_fee: Word,
}

impl BlockConstants {
    /// Generate a BlockConstants from an ethereum block, useful for testing.
    pub fn from_eth_block<TX>(
        block: &Block<TX>,
        chain_id: &Word,
        &coinbase: &Address,
    ) -> Self {
        Self {
            hash: block.hash.unwrap(),
            coinbase,
            timestamp: block.timestamp,
            number: block.number.unwrap(),
            difficulty: block.difficulty,
            gas_limit: block.gas_limit,
            chain_id: *chain_id,
            base_fee: block.base_fee_per_gas.unwrap(),
        }
    }

    /// Generate a new mock BlockConstants, useful for testing.
    pub fn mock() -> Self {
        BlockConstants {
            hash: Hash::from([0u8; 32]),
            coinbase: Address::from_str(
                "0x00000000000000000000000000000000c014ba5e",
            )
            .unwrap(),
            timestamp: Word::from(1633398551u64),
            number: U64([123456u64]),
            difficulty: Word::from(0x200000u64),
            gas_limit: Word::from(15_000_000u64),
            chain_id: Word::one(),
            base_fee: Word::from(97u64),
        }
    }
}

impl BlockConstants {
    #[allow(clippy::too_many_arguments)]
    /// Generates a new `BlockConstants` instance from it's fields.
    pub fn new(
        hash: Hash,
        coinbase: Address,
        timestamp: Word,
        number: U64,
        difficulty: Word,
        gas_limit: Word,
        chain_id: Word,
        base_fee: Word,
    ) -> BlockConstants {
        BlockConstants {
            hash,
            coinbase,
            timestamp,
            number,
            difficulty,
            gas_limit,
            chain_id,
            base_fee,
        }
    }
    #[inline]
    /// Return the hash of a block.
    pub fn hash(&self) -> &Hash {
        &self.hash
    }

    #[inline]
    /// Return the coinbase of a block.
    pub fn coinbase(&self) -> &Address {
        &self.coinbase
    }

    #[inline]
    /// Return the timestamp of a block.
    pub fn timestamp(&self) -> &Word {
        &self.timestamp
    }

    #[inline]
    /// Return the block number.
    pub fn number(&self) -> &U64 {
        &self.number
    }

    #[inline]
    /// Return the difficulty of a block.
    pub fn difficulty(&self) -> &Word {
        &self.difficulty
    }

    #[inline]
    /// Return the gas_limit of a block.
    pub fn gas_limit(&self) -> &Word {
        &self.gas_limit
    }

    #[inline]
    /// Return the chain ID associated to a block.
    pub fn chain_id(&self) -> &Word {
        &self.chain_id
    }

    #[inline]
    /// Return the base fee of a block.
    pub fn base_fee(&self) -> &Word {
        &self.base_fee
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// The target and index of an `Operation` in the context of an
/// `ExecutionTrace`.
pub struct OperationRef(Target, usize);

impl From<(Target, usize)> for OperationRef {
    fn from(op_ref_data: (Target, usize)) -> Self {
        match op_ref_data.0 {
            Target::Memory => Self(Target::Memory, op_ref_data.1),
            Target::Stack => Self(Target::Stack, op_ref_data.1),
            Target::Storage => Self(Target::Storage, op_ref_data.1),
        }
    }
}

impl OperationRef {
    /// Return the `OperationRef` as a `usize`.
    pub const fn as_usize(&self) -> usize {
        self.1
    }

    /// Return the [`Target`] op type of the `OperationRef`.
    pub const fn target(&self) -> Target {
        self.0
    }
}
