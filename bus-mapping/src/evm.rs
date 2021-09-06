//! Evm types needed for parsing instruction sets as well

pub(crate) mod gas;
pub(crate) mod instruction;
pub(crate) mod opcodes;

use crate::error::Error;
use core::str::FromStr;
use num::{BigUint, Num};
use serde::{Deserialize, Serialize};
pub use {
    gas::GasCost,
    instruction::Instruction,
    opcodes::{ids::OpcodeId, Opcode},
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

/// Represents a `MemoryAddress` of the EVM.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct MemoryAddress(pub(crate) usize);

impl MemoryAddress {
    /// Returns the zero address for Memory targets.
    pub const fn zero() -> MemoryAddress {
        MemoryAddress(0usize)
    }

    /// Return the little-endian byte representation of the word as a 32-byte
    /// array.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut array = [0u8; 32];
        array.copy_from_slice(&self.0.to_le_bytes());

        array
    }
}

impl From<MemoryAddress> for usize {
    fn from(addr: MemoryAddress) -> usize {
        addr.0
    }
}

impl FromStr for MemoryAddress {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(MemoryAddress(
            usize::from_str_radix(s, 16).map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}

/// Represents a `StackAddress` of the EVM.
/// The address range goes `TOP -> DOWN (1024, 0]`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct StackAddress(pub(crate) usize);

impl StackAddress {
    /// Generates a new StackAddress given a `usize`.
    pub const fn new(addr: usize) -> StackAddress {
        StackAddress(addr)
    }
}

impl From<StackAddress> for usize {
    fn from(addr: StackAddress) -> usize {
        addr.0
    }
}

impl From<usize> for StackAddress {
    fn from(addr: usize) -> StackAddress {
        StackAddress(addr)
    }
}

impl FromStr for StackAddress {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(StackAddress(
            usize::from_str_radix(s, 16).map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}

// XXX: Consider to move this to [u8;32] soon
/// Representation of an EVM word which is basically a 32-byte word.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct EvmWord(pub(crate) BigUint);

impl FromStr for EvmWord {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(EvmWord(
            BigUint::from_str_radix(s, 16)
                .map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}

macro_rules! impl_from_big_uint_wrappers {
    ($($t:ty),*) => {
        $(impl From<$t> for EvmWord {
            fn from(item: $t) -> EvmWord {
                EvmWord(BigUint::from(item))
            }
        })*
    };
}

impl_from_big_uint_wrappers!(u8, u16, u32, u64, u128, usize);

impl EvmWord {
    /// Return the little-endian byte representation of the word as a 32-byte
    /// array.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut array = [0u8; 32];
        let bytes = self.0.to_bytes_le();
        array[..bytes.len() - 1].copy_from_slice(&bytes[0..bytes.len() - 1]);

        array
    }

    /// Returns the underlying representation of the `EvmWord` as a [`BigUint`].
    pub fn as_big_uint(&self) -> &BigUint {
        &self.0
    }
}
