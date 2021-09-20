//! Doc this
use super::EvmWord;
use crate::Error;
use core::ops::{Deref, DerefMut};
use core::str::FromStr;

/// Represents a `MemoryAddress` of the EVM.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
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

impl_from_usize_wrappers!(
    MemoryAddress = MemoryAddress,
    (u8, u16, u32, usize, i32, i64)
);

impl FromStr for MemoryAddress {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(MemoryAddress(
            usize::from_str_radix(s, 16).map_err(|_| Error::EvmWordParsing)?,
        ))
    }
}

/// Represents a snapshot of the EVM memory state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memory(pub(crate) Vec<(MemoryAddress, EvmWord)>);

impl Deref for Memory {
    type Target = Vec<(MemoryAddress, EvmWord)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Memory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Memory {
    /// Generate an empty instance of EVM memory.
    pub const fn empty() -> Memory {
        Memory(Vec::new())
    }

    /// Generate an new instance of EVM memory given a `Vec<EvmWord>`.
    pub fn new(words: Vec<EvmWord>) -> Memory {
        Memory(
            words
                .iter()
                .cloned()
                .enumerate()
                .map(|(addr, word)| (MemoryAddress::from(addr * 32), word))
                .collect(),
        )
    }

    /// Returns the last memory region written at this execution step height.
    pub fn memory_addr(&self) -> MemoryAddress {
        self.0
            .last()
            .map(|(addr, _)| *addr)
            .unwrap_or_else(|| MemoryAddress::zero())
    }
}
