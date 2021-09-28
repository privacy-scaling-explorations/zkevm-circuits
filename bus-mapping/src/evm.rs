//! Evm types needed for parsing instruction sets as well

pub mod memory;
pub(crate) mod opcodes;
pub mod stack;

use crate::{error::Error, Gas};
use core::str::FromStr;
use serde::{Deserialize, Serialize};
pub use {
    memory::{Memory, MemoryAddress},
    opcodes::{ids::OpcodeId, Opcode},
    stack::{Stack, StackAddress},
};

/// Wrapper type over `usize` which represents the program counter of the Evm.
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize, PartialOrd, Ord,
)]
pub struct ProgramCounter(pub(crate) usize);

impl From<ProgramCounter> for usize {
    fn from(addr: ProgramCounter) -> usize {
        addr.0
    }
}

impl From<usize> for ProgramCounter {
    fn from(pc: usize) -> Self {
        ProgramCounter(pc)
    }
}

/// Wrapper type over `usize` which represents the global counter associated to
/// an [`ExecutionStep`](crate::exec_trace::ExecutionStep) or
/// [`Operation`](crate::operation::Operation). The purpose of the
/// `GlobalCounter` is to enforce that each Opcode/Instruction and Operation is
/// unique and just executed once.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct GlobalCounter(pub(crate) usize);

impl From<GlobalCounter> for usize {
    fn from(addr: GlobalCounter) -> usize {
        addr.0
    }
}

impl From<usize> for GlobalCounter {
    fn from(gc: usize) -> Self {
        GlobalCounter(gc)
    }
}

/// Representation of an EVM word which is basically a 32-byte word.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct EvmWord(pub(crate) [u8; 32]);

impl FromStr for EvmWord {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let decoding = hex::decode(s).map_err(|_| Error::EvmWordParsing)?;
        EvmWord::from_be_bytes(&decoding)
    }
}

impl From<EvmWord> for Vec<u8> {
    fn from(word: EvmWord) -> Self {
        word.inner().to_vec()
    }
}

impl_from_evm_word_wrappers!(u8, u16, u32, u64, u128, usize);

impl EvmWord {
    /// Return the big-endian byte representation of the word as a 32-byte
    /// array.
    pub const fn inner(&self) -> &[u8; 32] {
        &self.0
    }

    /// Generate an `EvmWord` from a slice of bytes in big-endian representation.
    pub fn from_be_bytes<T: AsRef<[u8]>>(bytes: T) -> Result<Self, Error> {
        if bytes.as_ref().len() > 32 {
            return Err(Error::EvmWordParsing);
        }
        let mut inner = [0u8; 32];
        inner[32 - bytes.as_ref().len()..].copy_from_slice(&bytes.as_ref());
        Ok(EvmWord(inner))
    }

    /// Generate an `EvmWord` from a slice of bytes in little-endian representation.
    pub fn from_le_bytes<T: AsRef<[u8]>>(bytes: T) -> Result<Self, Error> {
        if bytes.as_ref().len() > 32 {
            return Err(Error::EvmWordParsing);
        }
        let mut inner = [0u8; 32];
        inner[..bytes.as_ref().len()].copy_from_slice(&bytes.as_ref());
        inner.reverse();
        Ok(EvmWord(inner))
    }

    /// Returns an `EvmWord` as a 32-byte array in little endian representation.
    pub fn to_le_bytes(self) -> [u8; 32] {
        let mut bytes = self.0;
        bytes.reverse();
        bytes
    }

    /// Returns an `EvmWord` as a 32-byte array in big endian representation.
    pub fn to_be_bytes(self) -> [u8; 32] {
        *self.inner()
    }
}

/// Defines the gas consumed by an [`ExecutionStep`](crate::exec_trace::ExecutionStep)
/// as well as the gas left to operate.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct GasInfo {
    pub(crate) gas: Gas,
    pub(crate) gas_cost: GasCost,
}

impl GasInfo {
    /// Generates a new `GasInfo` instance from it's fields.
    pub fn new(gas: Gas, gas_cost: GasCost) -> GasInfo {
        GasInfo { gas, gas_cost }
    }

    /// Returns the gas left marked by a GasInfo instance.
    pub fn gas(&self) -> Gas {
        self.gas
    }

    /// Returns the gas consumed by an [`OpcodeId`] execution.
    pub fn gas_cost(&self) -> GasCost {
        self.gas_cost
    }
}

/// Gas Cost structure which is integrated inside [`GasInfo`].
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct GasCost(u64);

impl GasCost {
    /// Constant cost for quick step
    pub const QUICK: Self = Self(2);
    /// Constant cost for fastest step
    pub const FASTEST: Self = Self(3);
    /// Constant cost for fast step
    pub const FAST: Self = Self(5);
    /// Constant cost for mid step
    pub const MID: Self = Self(8);
    /// Constant cost for slow step
    pub const SLOW: Self = Self(10);
    /// Constant cost for ext step
    pub const EXT: Self = Self(20);
}

impl GasCost {
    /// Returns the `GasCost` as a `u64`.
    #[inline]
    pub const fn as_u64(&self) -> u64 {
        self.0
    }

    /// Returns the `GasCost` as a `usize`.
    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl From<u8> for GasCost {
    fn from(cost: u8) -> Self {
        GasCost(cost as u64)
    }
}

impl From<u64> for GasCost {
    fn from(cost: u64) -> Self {
        GasCost(cost)
    }
}

#[cfg(test)]
mod evm_tests {
    use super::*;

    #[test]
    fn evmword_bytes_serialization_trip() -> Result<(), Error> {
        let first_usize = 64536usize;
        // Parsing on both ways works.
        assert_eq!(
            EvmWord::from_le_bytes(&first_usize.to_le_bytes())?,
            EvmWord::from_be_bytes(&first_usize.to_be_bytes())?
        );
        let addr = EvmWord::from_le_bytes(&first_usize.to_le_bytes())?;
        assert_eq!(addr, EvmWord::from(first_usize));

        // Little endian export
        let le_obtained_usize = addr.to_le_bytes();
        let mut le_array = [0u8; 8];
        le_array.copy_from_slice(&le_obtained_usize[0..8]);

        // Big endian export
        let mut be_array = [0u8; 8];
        let be_obtained_usize = addr.to_be_bytes();
        be_array.copy_from_slice(&be_obtained_usize[24..32]);

        assert_eq!(first_usize, usize::from_le_bytes(le_array));
        assert_eq!(first_usize, usize::from_be_bytes(be_array));

        Ok(())
    }

    #[test]
    fn evmword_from_str() -> Result<(), Error> {
        let word_str =
            "000000000000000000000000000000000000000000000000000c849c24f39248";

        let word_from_u128 = EvmWord::from(3523505890234952u128);
        let word_from_str = EvmWord::from_str(&word_str)?;

        assert_eq!(word_from_u128, word_from_str);
        Ok(())
    }
}
