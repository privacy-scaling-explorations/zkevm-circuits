//! Doc this
use super::EvmWord;
use crate::Error;
use core::convert::{TryFrom, TryInto};
use core::ops::{Index, IndexMut};
use core::str::FromStr;

/// Represents a `MemoryAddress` of the EVM.
///
/// All `From` basic implementations assume that
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct MemoryAddress(pub(crate) usize);

impl TryFrom<EvmWord> for MemoryAddress {
    type Error = Error;

    fn try_from(word: EvmWord) -> Result<Self, Self::Error> {
        let addr: usize =
            word.0.try_into().map_err(|_| Error::MemAddressParsing)?;
        Ok(MemoryAddress(addr))
    }
}

impl MemoryAddress {
    /// Returns the zero address for Memory targets.
    pub const fn zero() -> MemoryAddress {
        MemoryAddress(0usize)
    }

    /// Return the little-endian byte representation of the word as a 32-byte
    /// array.
    pub fn to_bytes(self) -> [u8; 32] {
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
            usize::from_str_radix(s, 16)
                .map_err(|_| Error::MemAddressParsing)?,
        ))
    }
}

/// Represents a snapshot of the EVM memory state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memory(pub(crate) Vec<EvmWord>);

impl Index<MemoryAddress> for Memory {
    type Output = EvmWord;
    fn index(&self, index: MemoryAddress) -> &Self::Output {
        // MemoryAddress is in base 16. Therefore since the vec is not, we need to shift the addr.
        &self.0[index.0 >> 5]
    }
}

impl IndexMut<MemoryAddress> for Memory {
    fn index_mut(&mut self, index: MemoryAddress) -> &mut Self::Output {
        // MemoryAddress is in base 16. Therefore since the vec is not, we need to shift the addr.
        &mut self.0[index.0 >> 5]
    }
}

impl Memory {
    /// Generate an empty instance of EVM memory.
    pub const fn empty() -> Memory {
        Memory(Vec::new())
    }

    /// Generate an new instance of EVM memory given a `Vec<EvmWord>`.
    pub fn new(words: Vec<EvmWord>) -> Memory {
        Memory(words)
    }

    /// Returns the last memory address written at this execution step height.
    pub fn last_addr(&self) -> MemoryAddress {
        (self.0.len() << 4).into()
    }
}
