pub mod container;

use super::evm::{EvmWord, GlobalCounter, MemoryAddress, StackAddress};
use core::cmp::Ordering;

/// Doc
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RW {
    /// Doc
    READ,
    /// Doc
    WRITE,
}

/// Doc
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum Target {
    /// Doc
    Memory,
    /// Doc
    Stack,
    /// Doc
    Storage,
}

/// Doc
pub trait Operation
where
    Self: Sized + Clone + Ord + PartialOrd,
{
    /// Doc
    type Address;
    /// Doc
    fn rw(&self) -> RW;
    /// Doc
    fn target(&self) -> Target;
    /// Doc
    fn gc(&self) -> GlobalCounter;
    /// Doc
    fn address(&self) -> &Self::Address;
    /// Doc
    fn value(&self) -> &EvmWord;
}

/// Doc
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryOp {
    rw: RW,
    gc: GlobalCounter,
    addr: MemoryAddress,
    value: EvmWord,
}

impl Operation for MemoryOp {
    type Address = MemoryAddress;
    fn rw(&self) -> RW {
        self.rw
    }

    fn target(&self) -> Target {
        Target::Memory
    }

    fn gc(&self) -> GlobalCounter {
        self.gc
    }

    fn address(&self) -> &Self::Address {
        &self.addr
    }

    fn value(&self) -> &EvmWord {
        &self.value
    }
}

impl PartialOrd for MemoryOp {
    fn partial_cmp(&self, other: &MemoryOp) -> Option<Ordering> {
        match self.address().partial_cmp(other.address()) {
            None => None,
            Some(ord) => match ord {
                std::cmp::Ordering::Equal => self.gc().partial_cmp(&other.gc()),
                _ => Some(ord),
            },
        }
    }
}

impl Ord for MemoryOp {
    fn cmp(&self, other: &MemoryOp) -> Ordering {
        let ord = self.address().cmp(other.address());
        match ord {
            std::cmp::Ordering::Equal => self.gc().cmp(&other.gc()),
            _ => ord,
        }
    }
}

/// Doc
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackOp {
    rw: RW,
    gc: GlobalCounter,
    addr: StackAddress, // Create a new type
    value: EvmWord,
}

impl Operation for StackOp {
    type Address = StackAddress;
    fn rw(&self) -> RW {
        self.rw
    }

    fn target(&self) -> Target {
        Target::Stack
    }

    fn gc(&self) -> GlobalCounter {
        self.gc
    }

    fn address(&self) -> &Self::Address {
        &self.addr
    }

    fn value(&self) -> &EvmWord {
        &self.value
    }
}

impl PartialOrd for StackOp {
    fn partial_cmp(&self, other: &StackOp) -> Option<Ordering> {
        match self.address().partial_cmp(other.address()) {
            None => None,
            Some(ord) => match ord {
                std::cmp::Ordering::Equal => self.gc().partial_cmp(&other.gc()),
                _ => Some(ord),
            },
        }
    }
}

impl Ord for StackOp {
    fn cmp(&self, other: &StackOp) -> Ordering {
        let ord = self.address().cmp(other.address());
        match ord {
            std::cmp::Ordering::Equal => self.gc().cmp(&other.gc()),
            _ => ord,
        }
    }
}

/// Doc
pub struct StorageOp; // Update with https://hackmd.io/kON1GVL6QOC6t5tf_OTuKA with Han's review
