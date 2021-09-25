//! Evm types needed for parsing instruction sets as well

pub mod memory;
pub(crate) mod opcodes;
pub mod stack;

use crate::{error::Error, Gas};
use core::str::FromStr;
use num::{BigUint, Num};
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

impl From<EvmWord> for [u8; 32] {
    fn from(word: EvmWord) -> Self {
        word.to_bytes()
    }
}

impl From<EvmWord> for Vec<u8> {
    fn from(word: EvmWord) -> Self {
        word.to_bytes().to_vec()
    }
}

impl_from_big_uint_wrappers!(
    EvmWord = EvmWord,
    (u8, u16, u32, u64, u128, usize)
);

impl EvmWord {
    /// Return the little-endian byte representation of the word as a 32-byte
    /// array.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut array = [0u8; 32];
        let bytes = self.0.to_bytes_le();
        array[..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);

        array
    }

    /// Generate an `EvmWord` from a slice of bytes.
    pub fn from_bytes<T: AsRef<[u8]>>(bytes: T) -> Self {
        EvmWord(BigUint::from_bytes_le(bytes.as_ref()))
    }

    /// Returns the underlying representation of the `EvmWord` as a [`BigUint`].
    pub fn as_big_uint(&self) -> &BigUint {
        &self.0
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
