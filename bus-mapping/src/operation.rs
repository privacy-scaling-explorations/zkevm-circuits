pub mod container;

use super::evm::{Address, EvmWord, GlobalCounter, MemoryAddress, StackAddress};
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Target {
    /// Doc
    Memory(MemoryOp),
    /// Doc
    Stack(StackOp),
    /// Doc
    Storage(StorageOp),
}

/// Doc
pub trait Operation
where
    Self: Sized + Clone + Ord + PartialOrd,
{
    /// Doc
    fn rw(&self) -> RW;
    /// Doc
    fn gc(&self) -> GlobalCounter;
    /// Doc
    fn address(&self) -> Address;
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

impl Operation for Target {
    fn rw(&self) -> RW {
        match self {
            Self::Memory(op) => op.rw,
            Self::Stack(op) => op.rw,
            Self::Storage(_) => unimplemented!(),
        }
    }

    fn gc(&self) -> GlobalCounter {
        match self {
            Self::Memory(op) => op.gc,
            Self::Stack(op) => op.gc,
            Self::Storage(_) => unimplemented!(),
        }
    }

    fn address(&self) -> Address {
        match self {
            Self::Memory(op) => op.addr.clone().into(),
            Self::Stack(op) => op.addr.clone().into(),
            Self::Storage(_) => unimplemented!(),
        }
    }

    fn value(&self) -> &EvmWord {
        match self {
            Self::Memory(op) => &op.value,
            Self::Stack(op) => &op.value,
            Self::Storage(_) => unimplemented!(),
        }
    }
}

impl PartialOrd for Target {
    fn partial_cmp(&self, other: &Target) -> Option<Ordering> {
        match self.address().partial_cmp(&other.address()) {
            None => None,
            Some(ord) => match ord {
                std::cmp::Ordering::Equal => self.gc().partial_cmp(&other.gc()),
                _ => Some(ord),
            },
        }
    }
}

impl Ord for Target {
    fn cmp(&self, other: &Target) -> Ordering {
        let ord = self.address().cmp(&other.address());
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

/// Doc
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct StorageOp; // Update with https://hackmd.io/kON1GVL6QOC6t5tf_OTuKA with Han's review
