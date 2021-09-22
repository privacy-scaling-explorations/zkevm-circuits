//! Doc this
use crate::evm::EvmWord;
use crate::Error;
use core::ops::{Deref, DerefMut};
use core::str::FromStr;

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

// Mostly impl for testing.
impl_from_usize_wrappers!(
    StackAddress = StackAddress,
    (u8, u16, u32, usize, i32, i64)
);

impl From<StackAddress> for usize {
    fn from(addr: StackAddress) -> usize {
        addr.0
    }
}

impl FromStr for StackAddress {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = usize::from_str_radix(s, 16)
            .map_err(|_| Error::StackAddressParsing)?;
        // Stack only has 1023 slots avaliable.
        if value >= 1024 {
            return Err(Error::StackAddressParsing);
        };
        Ok(StackAddress(value))
    }
}

/// Represents a snapshot of the EVM stack state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Stack(pub(crate) Vec<EvmWord>);

impl Stack {
    /// Generate an empty instance of EVM stack.
    pub const fn empty() -> Stack {
        Stack(Vec::new())
    }

    /// Generate an new instance of EVM stack given a `Vec<EvmWord>`.
    pub const fn new(item: Vec<EvmWord>) -> Stack {
        Stack(item)
    }

    /// Returns the first free `StackAddress` avaliable/free.
    pub fn stack_pointer(&self) -> StackAddress {
        // Stack has 1024 slots.
        // First allocation slot for us in the stack is 1023.
        StackAddress::from(1023 - self.0.len())
    }

    /// Returns the last filled `StackAddress`.
    pub fn last_filled(&self) -> StackAddress {
        StackAddress::from(1024 - self.0.len())
    }
}

impl Deref for Stack {
    type Target = Vec<EvmWord>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Stack {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
