//! Evm types needed for parsing instruction sets as well

pub mod memory;
pub(crate) mod opcodes;
pub mod stack;
pub mod storage;

use crate::error::{EthAddressParsingError, EvmWordParsingError};
use core::str::FromStr;
use serde::{Deserialize, Serialize};
use std::fmt;
pub use {
    memory::{Memory, MemoryAddress},
    opcodes::{ids::OpcodeId, Opcode},
    stack::{Stack, StackAddress},
    storage::Storage,
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

impl ProgramCounter {
    /// Increase Self by one
    pub fn inc(&mut self) {
        self.0 += 1;
    }

    /// Increase Self by one and return the value before the increase.
    pub fn inc_pre(&mut self) -> Self {
        let pre = *self;
        self.inc();
        pre
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

impl Default for GlobalCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl GlobalCounter {
    /// Create a new GlobalCounter with the initial default value
    pub fn new() -> Self {
        Self(0)
    }

    /// Increase Self by one
    pub fn inc(&mut self) {
        self.0 += 1;
    }

    /// Increase Self by one and return the value before the increase.
    pub fn inc_pre(&mut self) -> Self {
        let pre = *self;
        self.inc();
        pre
    }
}

/// Representation of an EVM word which is basically a 32-byte word.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct EvmWord(pub(crate) [u8; 32]);

impl Default for EvmWord {
    fn default() -> Self {
        EvmWord([0; 32])
    }
}

impl FromStr for EvmWord {
    type Err = EvmWordParsingError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        const MAX_LEN: usize = 32 * 2; // Word is 256 bits, so that's 32 bytes, * 2 for hex
        let s = s.strip_prefix("0x").unwrap_or(s);
        if s.len() > MAX_LEN {
            return Err(EvmWordParsingError::TooLong);
        }
        // Copy s to a fixed-length buffer to make it even-length.
        let mut buf = [b'0'; MAX_LEN];
        buf[MAX_LEN - s.len()..].copy_from_slice(s.as_bytes());
        let decoding = hex::decode(&buf).map_err(EvmWordParsingError::Hex)?;
        EvmWord::from_be_bytes(&decoding)
    }
}

impl fmt::Display for EvmWord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}

impl From<EvmWord> for Vec<u8> {
    fn from(word: EvmWord) -> Self {
        word.inner().to_vec()
    }
}

impl_from_evm_word_wrappers!(u8, u16, u32, u64, u128, usize);

impl Serialize for EvmWord {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_hex())
    }
}

impl EvmWord {
    /// Return the length of this type in bytes.
    pub const fn len() -> usize {
        32 // Word is 256 bits, so that's 32 bytes
    }

    /// Return the big-endian byte representation of the word as a 32-byte
    /// array.
    pub const fn inner(&self) -> &[u8; 32] {
        &self.0
    }

    /// Generate an `EvmWord` from a slice of bytes in big-endian
    /// representation.
    pub fn from_be_bytes<T: AsRef<[u8]>>(
        bytes: T,
    ) -> Result<Self, EvmWordParsingError> {
        if bytes.as_ref().len() > 32 {
            return Err(EvmWordParsingError::TooLong);
        }
        let mut inner = [0u8; 32];
        inner[32 - bytes.as_ref().len()..].copy_from_slice(bytes.as_ref());
        Ok(EvmWord(inner))
    }

    /// Generate an `EvmWord` from a slice of bytes in little-endian
    /// representation.
    pub fn from_le_bytes<T: AsRef<[u8]>>(
        bytes: T,
    ) -> Result<Self, EvmWordParsingError> {
        if bytes.as_ref().len() > 32 {
            return Err(EvmWordParsingError::TooLong);
        }
        let mut inner = [0u8; 32];
        inner[..bytes.as_ref().len()].copy_from_slice(bytes.as_ref());
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

    /// Returns an `EvmWord` as a hex string representation.
    pub fn to_hex(self) -> String {
        hex::encode(self.to_be_bytes())
    }
}

/// Representation of an Ethereum Address which is basically a 20-byte array.
#[derive(Debug, Eq, PartialEq, Clone, Copy, PartialOrd, Ord)]
pub struct EthAddress(pub(crate) [u8; 20]);

impl FromStr for EthAddress {
    type Err = EthAddressParsingError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.strip_prefix("0x").unwrap_or(s);
        if s.len() != Self::len() * 2 {
            return Err(EthAddressParsingError::BadLength);
        }
        let decoding = hex::decode(s).map_err(EthAddressParsingError::Hex)?;
        Self::from_bytes(&decoding)
    }
}

impl Serialize for EthAddress {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_word().to_hex())
    }
}

impl EthAddress {
    /// Return the length of this type in bytes.
    pub const fn len() -> usize {
        20 // Address is 160 bits, so that's 20 bytes
    }

    /// Return the big-endian byte representation of the Ethereum Address as a 02-byte
    /// array.
    pub const fn inner(&self) -> &[u8; 20] {
        &self.0
    }

    /// Returns the zero address.
    pub fn zero() -> Self {
        Self::from_str("0x0000000000000000000000000000000000000000").unwrap()
    }

    /// Generate an `EthAddress` from a slice of bytes.
    pub fn from_bytes<T: AsRef<[u8]>>(
        bytes: T,
    ) -> Result<Self, EthAddressParsingError> {
        if bytes.as_ref().len() != Self::len() {
            return Err(EthAddressParsingError::BadLength);
        }
        let mut inner = [0u8; Self::len()];
        inner.copy_from_slice(bytes.as_ref());
        Ok(EthAddress(inner))
    }

    /// Return an `EvmWord` representation of the `EthAddress`.
    pub fn to_word(self) -> EvmWord {
        let mut inner = [0u8; 32];
        inner[32 - Self::len()..].copy_from_slice(self.inner().as_ref());
        EvmWord(inner)
    }
}

/// Defines the gas consumed by an
/// [`ExecutionStep`](crate::exec_trace::ExecutionStep) as well as the gas left
/// to operate.
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct GasCost(u64);

impl GasCost {
    /// Constant cost for free step
    pub const ZERO: Self = Self(0);
    /// Constant cost for jumpdest step, only it takes one gas
    pub const ONE: Self = Self(1);
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
    /// Constant cost for a cold SLOAD
    pub const COLD_SLOAD_COST: Self = Self(2100);
    /// Constant cost for a cold account access
    pub const COLD_ACCOUNT_ACCESS_COST: Self = Self(2600);
    /// Constant cost for a warm storage read
    pub const WARM_STORAGE_READ_COST: Self = Self(100);
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
    use crate::Error;

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
        let word_from_str = EvmWord::from_str(word_str)?;

        assert_eq!(word_from_u128, word_from_str);
        Ok(())
    }

    #[test]
    fn ethaddress() {
        // Test from_str
        assert_eq!(
            EthAddress::from_str("0x9a0C63EBb78B35D7c209aFbD299B056098b5439b")
                .unwrap(),
            EthAddress([
                154, 12, 99, 235, 183, 139, 53, 215, 194, 9, 175, 189, 41, 155,
                5, 96, 152, 181, 67, 155
            ])
        );
        assert_eq!(
            EthAddress::from_str("9a0C63EBb78B35D7c209aFbD299B056098b5439b")
                .unwrap(),
            EthAddress([
                154, 12, 99, 235, 183, 139, 53, 215, 194, 9, 175, 189, 41, 155,
                5, 96, 152, 181, 67, 155
            ])
        );

        // Test from_str Errors
        assert_eq!(
            &format!(
                "{:?}",
                EthAddress::from_str(
                    "0x9a0C63EBb78B35D7c209aFbD299B056098b543"
                )
            ),
            "Err(BadLength)",
        );
        assert_eq!(
            &format!(
                "{:?}",
                EthAddress::from_str(
                    "0x9a0C63EBb78B35D7c209aFbD299B056098b543XY"
                )
            ),
            "Err(Hex(InvalidHexCharacter { c: 'X', index: 38 }))",
        );

        // Test to_word
        assert_eq!(
            EthAddress::from_str("0x0000000000000000000000000000000000000001")
                .unwrap()
                .to_word(),
            EvmWord::from(1u32),
        );
    }
}
