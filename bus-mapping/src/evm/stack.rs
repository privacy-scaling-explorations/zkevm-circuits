//! Doc this
use crate::evm::EvmWord;
use crate::Error;
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
        let s = s.strip_prefix("0x").unwrap_or(s);
        let value = usize::from_str_radix(s, 16)
            .map_err(|_| Error::StackAddressParsing)?;
        // Stack only has 1023 slots avaliable.
        if value >= 1024 {
            return Err(Error::InvalidStackPointer);
        };
        Ok(StackAddress(value))
    }
}

/// Represents a snapshot of the EVM stack state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Stack(pub(crate) Vec<EvmWord>);

impl<T: Into<Vec<EvmWord>>> From<T> for Stack {
    fn from(words: T) -> Self {
        Stack(words.into())
    }
}

impl Stack {
    /// Generate a new instance of EVM stack.
    pub const fn new() -> Stack {
        Stack(vec![])
    }

    /// Generates a `Stack` instance from the given slice.
    pub fn from_slice(words: &[EvmWord]) -> Self {
        Stack(words.into())
    }

    /// Generates a `Stack` instance from the given vec.
    pub const fn from_vec(words: Vec<EvmWord>) -> Self {
        Stack(words)
    }

    /// Returns the first avaliable/free `StackAddress`.
    pub fn stack_pointer(&self) -> StackAddress {
        // Stack has 1024 slots.
        // First allocation slot for us in the stack is 1023.
        StackAddress::from(1023 - self.0.len())
    }

    /// Returns the last filled `StackAddress`.
    pub fn last_filled(&self) -> StackAddress {
        StackAddress::from(1024 - self.0.len())
    }

    /// Returns the second last filled `StackAddress`.
    pub fn nth_last_filled(&self, nth: usize) -> StackAddress {
        StackAddress::from(1024 - self.0.len() + nth)
    }

    /// Returns the last [`EvmWord`] allocated in the `Stack`.
    pub fn last(&self) -> Option<&EvmWord> {
        self.0.last()
    }

    /// Returns the second last [`EvmWord`] allocated in the `Stack`.
    pub fn nth_last(&self, nth: usize) -> Option<&EvmWord> {
        self.0.get(self.0.len() - (nth + 1))
    }
}

#[cfg(test)]
mod stack_tests {
    use super::*;

    fn setup_stack(stack_value: [&str; 3]) -> Stack {
        Stack::from_vec(vec![
            EvmWord::from_str(stack_value[0]).unwrap(),
            EvmWord::from_str(stack_value[1]).unwrap(),
            EvmWord::from_str(stack_value[2]).unwrap(),
        ])
    }

    #[test]
    fn stack_addr_conversion() -> Result<(), Error> {
        let first_usize = 1023usize;
        let addr1 = StackAddress::from(first_usize);
        let addr2 = StackAddress::from_str("0x3ff")?;

        assert_eq!(addr1.0, first_usize);
        assert_eq!(addr2.0, first_usize);
        Ok(())
    }

    #[test]
    fn stack_pointer() -> Result<(), Error> {
        let stack = setup_stack(["0x15", "0x16", "0x17"]);

        assert_eq!(stack.stack_pointer(), StackAddress::from(1020));
        assert_eq!(stack.last_filled(), StackAddress::from(1021));
        assert_eq!(stack.nth_last_filled(1), StackAddress::from(1022));
        Ok(())
    }

    #[test]
    fn stack_get_value() -> Result<(), Error> {
        let stack = setup_stack(["0x15", "0x16", "0x17"]);

        assert_eq!(stack.last().unwrap(), &EvmWord::from_str("0x17")?);
        assert_eq!(stack.nth_last(1).unwrap(), &EvmWord::from_str("0x16")?);
        Ok(())
    }
}
