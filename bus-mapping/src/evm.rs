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
        array[..bytes.len() - 1].copy_from_slice(&bytes[0..bytes.len() - 1]);

        array
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
    pub(crate) gas_cost: Gas,
}

impl GasInfo {
    /// Generates a new `GasInfo` instance from it's fields.
    pub fn new(gas: Gas, gas_cost: Gas) -> GasInfo {
        GasInfo { gas, gas_cost }
    }

    /// Returns the gas left marked by a GasInfo instance.
    pub fn gas_left(&self) -> Gas {
        self.gas
    }

    /// Returns the gas consumed by an [`Instruction`] execution.
    pub fn gas_consumed(&self) -> Gas {
        self.gas_cost
    }
}
