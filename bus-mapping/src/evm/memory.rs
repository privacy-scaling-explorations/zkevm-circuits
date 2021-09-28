//! Doc this
use super::EvmWord;
use crate::Error;
use core::convert::TryFrom;
use core::ops::{
    Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign,
};
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
    pub fn to_le_bytes(self) -> [u8; 32] {
        let mut array = [0u8; 32];
        let bytes = self.0.to_le_bytes();
        array[..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);

        array
    }

    /// Return the big-endian byte representation of the word as a 32-byte
    /// array.
    pub fn to_be_bytes(self) -> [u8; 32] {
        let mut array = [0u8; 32];
        let bytes = self.0.to_be_bytes();
        array[32 - bytes.len()..].copy_from_slice(&bytes[0..bytes.len()]);

        array
    }

    /// Generate a MemoryAddress from the provided set of little-endian bytes.
    pub fn from_le_bytes<T: AsRef<[u8]>>(bytes: T) -> Result<Self, Error> {
        if bytes.as_ref().len() > core::mem::size_of::<usize>() {
            return Err(Error::InvalidMemoryPointer);
        }
        let mut array = [0u8; core::mem::size_of::<usize>()];
        array[..]
            .copy_from_slice(&bytes.as_ref()[..core::mem::size_of::<usize>()]);
        Ok(MemoryAddress::from(usize::from_le_bytes(array)))
    }

    /// Generate a MemoryAddress from the provided set of big-endian bytes.
    pub fn from_be_bytes<T: AsRef<[u8]>>(bytes: T) -> Result<Self, Error> {
        if bytes.as_ref().len() > core::mem::size_of::<usize>() {
            return Err(Error::InvalidMemoryPointer);
        }
        let mut array = [0u8; core::mem::size_of::<usize>()];
        array[..]
            .copy_from_slice(&bytes.as_ref()[..core::mem::size_of::<usize>()]);
        Ok(MemoryAddress::from(usize::from_be_bytes(array)))
    }
}

impl TryFrom<EvmWord> for MemoryAddress {
    type Error = Error;

    fn try_from(word: EvmWord) -> Result<Self, Self::Error> {
        let (should_be_zeroes, usize_bytes) =
            word.inner().split_at(32 - core::mem::size_of::<usize>());
        if should_be_zeroes != [0u8; 32 - core::mem::size_of::<usize>()] {
            return Err(Error::WordToMemAddr);
        }
        let mut arr = [0u8; core::mem::size_of::<usize>()];
        arr.copy_from_slice(usize_bytes);
        Ok(MemoryAddress(usize::from_be_bytes(arr)))
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

impl Add<&MemoryAddress> for &MemoryAddress {
    type Output = MemoryAddress;

    fn add(self, rhs: &MemoryAddress) -> Self::Output {
        MemoryAddress(self.0 + rhs.0)
    }
}

define_add_variants!(
    LHS = MemoryAddress,
    RHS = MemoryAddress,
    Output = MemoryAddress
);

impl<'b> AddAssign<&'b MemoryAddress> for MemoryAddress {
    fn add_assign(&mut self, _rhs: &'b MemoryAddress) {
        *self = *self + _rhs;
    }
}

define_add_assign_variants!(LHS = MemoryAddress, RHS = MemoryAddress);

impl Sub<&MemoryAddress> for &MemoryAddress {
    type Output = MemoryAddress;

    fn sub(self, rhs: &MemoryAddress) -> Self::Output {
        MemoryAddress(self.0 - rhs.0)
    }
}

define_sub_variants!(
    LHS = MemoryAddress,
    RHS = MemoryAddress,
    Output = MemoryAddress
);

impl<'b> SubAssign<&'b MemoryAddress> for MemoryAddress {
    fn sub_assign(&mut self, _rhs: &'b MemoryAddress) {
        *self = *self - _rhs;
    }
}

define_sub_assign_variants!(LHS = MemoryAddress, RHS = MemoryAddress);

impl Mul<&MemoryAddress> for &MemoryAddress {
    type Output = MemoryAddress;

    fn mul(self, rhs: &MemoryAddress) -> Self::Output {
        MemoryAddress(self.0 * rhs.0)
    }
}

define_mul_variants!(
    LHS = MemoryAddress,
    RHS = MemoryAddress,
    Output = MemoryAddress
);

impl<'b> MulAssign<&'b MemoryAddress> for MemoryAddress {
    fn mul_assign(&mut self, _rhs: &'b MemoryAddress) {
        *self = *self * _rhs;
    }
}

define_mul_assign_variants!(LHS = MemoryAddress, RHS = MemoryAddress);

/// Represents a snapshot of the EVM memory state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memory(pub(crate) Vec<u8>);

impl From<Vec<u8>> for Memory {
    fn from(vec: Vec<u8>) -> Self {
        Memory(vec)
    }
}

impl Index<MemoryAddress> for Memory {
    type Output = u8;
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

define_range_index_variants!(
    IN_RANGE = usize,
    OUT_RANGE = MemoryAddress,
    STRUCT_CONTAINER = Memory,
    INDEX_OUTPUT = [u8]
);

impl Memory {
    /// Generate an empty instance of EVM memory.
    pub const fn empty() -> Memory {
        Memory(Vec::new())
    }

    /// Generate an new instance of EVM memory given a `Vec<u8>`.
    pub fn new(words: Vec<u8>) -> Memory {
        Memory(words)
    }

    /// Pushes a set of bytes or an [`EvmWord`] in the last `Memory` position.
    pub fn push<T: AsRef<[u8]>>(&mut self, input: T) {
        self.0.extend(input.as_ref())
    }

    /// Returns the last memory address written at this execution step height.
    pub fn last_filled_addr(&self) -> MemoryAddress {
        self.0.len().into()
    }

    /// Reads an entire [`EvmWord`] which starts at the provided [`MemoryAddress`] `addr` and
    /// finnishes at `addr + 32`.
    pub fn read_word(&self, addr: MemoryAddress) -> Result<EvmWord, Error> {
        // Ensure that the stack is big enough to have values in the range `[addr, addr+32)`.
        if self.0.len() < addr.0 + 32 {
            return Err(Error::InvalidMemoryPointer);
        }

        // Now we know that the indexing will not panic.
        EvmWord::from_be_bytes(&self[addr..addr + MemoryAddress::from(32)])
    }
}

#[cfg(test)]
mod memory_tests {
    use std::convert::TryInto;

    use super::*;

    #[test]
    fn evmword_mem_addr_conversion() -> Result<(), Error> {
        let first_usize = 64536usize;
        let word = EvmWord::from(first_usize);
        let addr = MemoryAddress::from(first_usize);
        let obtained_addr: MemoryAddress = word.try_into()?;

        assert_eq!(addr, obtained_addr);
        Ok(())
    }

    #[test]
    fn mem_addr_bytes_serialization_trip() -> Result<(), Error> {
        let first_usize = 64536usize;
        // Parsing on both ways works.
        assert_eq!(
            MemoryAddress::from_le_bytes(&first_usize.to_le_bytes())?,
            MemoryAddress::from_be_bytes(&first_usize.to_be_bytes())?
        );
        let addr = MemoryAddress::from_le_bytes(&first_usize.to_le_bytes())?;
        assert_eq!(addr, MemoryAddress::from(first_usize));

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
    fn push_and_read_works() -> Result<(), Error> {
        let mem_map = Memory(
            EvmWord::from(0u8)
                .inner()
                .iter()
                .chain(EvmWord::from(0u8).inner())
                .chain(EvmWord::from(0x80u8).inner())
                .copied()
                .collect(),
        );

        // At this point at position [0x40, 0x80) we've allocated the `0x80` value.

        // If we read a word at addr `0x40` we should get `0x80`.
        assert_eq!(
            mem_map.read_word(MemoryAddress::from(0x40))?,
            EvmWord::from(0x80u8)
        );

        Ok(())
    }
}
