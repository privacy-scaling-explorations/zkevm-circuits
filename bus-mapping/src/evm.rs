//! Evm types needed for parsing instruction sets as well

pub(crate) mod instruction;
pub(crate) mod opcodes;

use crate::error::Error;
use core::{convert::TryInto, str::FromStr};
pub(crate) use instruction::Instruction;
use lazy_static::lazy_static;
use num::{BigUint, Num, Zero};
use serde::{Deserialize, Serialize};

lazy_static! {
    /// Ref to zero addr for Memory
    pub(crate) static ref MEM_ADDR_ZERO: MemoryAddress = MemoryAddress(BigUint::zero());
}

/// Doc
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize, PartialOrd, Ord)]
pub(crate) struct ProgramCounter(pub(crate) usize);

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

/// Doc
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct GlobalCounter(pub(crate) usize);

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

/// Doc
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct MemoryAddress(pub(crate) BigUint);

impl MemoryAddress {
    pub fn zero() -> MemoryAddress {
        MemoryAddress(BigUint::zero())
    }
}

impl From<MemoryAddress> for BigUint {
    fn from(addr: MemoryAddress) -> BigUint {
        addr.0
    }
}

impl FromStr for MemoryAddress {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(MemoryAddress(
            BigUint::from_str_radix(s, 16).map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}

/// Doc
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct StackAddress(pub(crate) usize);

impl StackAddress {
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
            BigUint::from_str_radix(s, 16)
                .map_err(|_| Error::EvmWordParsing)
                .map(|biguint| {
                    biguint
                        .try_into()
                        .map_err(|_| Error::EvmWordParsing)
                        .expect("Map_err should be applied")
                })
                .map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}

/// Doc
// XXX: Consider to move this to [u8;32] soon
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct EvmWord(pub(crate) BigUint);

impl FromStr for EvmWord {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(EvmWord(
            BigUint::from_str_radix(s, 16).map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}
