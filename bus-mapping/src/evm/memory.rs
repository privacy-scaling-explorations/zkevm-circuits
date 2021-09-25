//! Doc this
use super::EvmWord;
use crate::Error;
use core::convert::{TryFrom, TryInto};
use core::ops::{
    Add, AddAssign, Index, IndexMut, Mul, MulAssign, Range, RangeFrom,
    RangeFull, RangeTo, RangeToInclusive, Sub, SubAssign,
};
use core::str::FromStr;

/// Represents a `MemoryAddress` of the EVM.
///
/// All `From` basic implementations assume that
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct MemoryAddress(pub(crate) usize);

impl MemoryAddress {
    /// Returns the zero address for Memory targets.
    pub const fn zero() -> MemoryAddress {
        MemoryAddress(0usize)
    }

    /// Return the little-endian byte representation of the word as a 32-byte
    /// array.
    pub fn to_bytes(self) -> [u8; 32] {
        let mut array = [0u8; 32];
        let bytes = self.0.to_le_bytes();
        array[..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);

        array
    }

    /// Generate a MemoryAddress from the provided set of bytes.
    pub fn from_bytes<T: AsRef<[u8]>>(bytes: T) -> Self {
        let mut array = [0u8; core::mem::size_of::<usize>()];
        array[..]
            .copy_from_slice(&bytes.as_ref()[..core::mem::size_of::<usize>()]);
        MemoryAddress::from(usize::from_le_bytes(array))
    }
}

impl TryFrom<EvmWord> for MemoryAddress {
    type Error = Error;

    fn try_from(word: EvmWord) -> Result<Self, Self::Error> {
        let addr: usize =
            word.0.try_into().map_err(|_| Error::MemAddressParsing)?;
        Ok(MemoryAddress(addr))
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

impl Index<Range<MemoryAddress>> for Memory {
    type Output = [u8];

    #[inline]
    fn index(&self, index: Range<MemoryAddress>) -> &Self::Output {
        &self.0[..][convert_range(index)]
    }
}

impl Index<RangeFull> for Memory {
    type Output = [u8];

    #[inline]
    fn index(&self, _index: RangeFull) -> &Self::Output {
        &self.0[..]
    }
}

impl Index<RangeTo<MemoryAddress>> for Memory {
    type Output = [u8];

    #[inline]
    fn index(&self, index: RangeTo<MemoryAddress>) -> &Self::Output {
        &self.0[..][convert_range_to(index)]
    }
}

impl Index<RangeFrom<MemoryAddress>> for Memory {
    type Output = [u8];

    #[inline]
    fn index(&self, index: RangeFrom<MemoryAddress>) -> &Self::Output {
        &self.0[..][convert_range_from(index)]
    }
}

impl Index<RangeToInclusive<MemoryAddress>> for Memory {
    type Output = [u8];

    #[inline]
    fn index(&self, index: RangeToInclusive<MemoryAddress>) -> &Self::Output {
        &self.0[..][convert_range_to_inclusive(index)]
    }
}

fn convert_range(range: Range<MemoryAddress>) -> Range<usize> {
    Range {
        start: range.start.0,
        end: range.end.0,
    }
}

fn convert_range_from(range: RangeFrom<MemoryAddress>) -> RangeFrom<usize> {
    RangeFrom {
        start: range.start.0,
    }
}

fn convert_range_to(range: RangeTo<MemoryAddress>) -> RangeTo<usize> {
    RangeTo { end: range.end.0 }
}

fn convert_range_to_inclusive(
    range: RangeToInclusive<MemoryAddress>,
) -> RangeToInclusive<usize> {
    RangeToInclusive { end: range.end.0 }
}

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
    pub fn read_word(&self, addr: MemoryAddress) -> EvmWord {
        EvmWord::from_bytes(
            &self[addr..addr + MemoryAddress::from(32)].as_ref(),
        )
    }
}
