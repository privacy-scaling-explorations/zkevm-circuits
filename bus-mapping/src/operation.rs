pub mod container;

use crate::error::Error;

use super::evm::{EvmWord, GlobalCounter, MemoryAddress, StackAddress};
use core::cmp::Ordering;
use core::fmt::Debug;
use std::convert::TryFrom;

/// Doc
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RW {
    /// Doc
    READ,
    /// Doc
    WRITE,
}

/// Doc
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum Target {
    /// Doc
    Memory,
    /// Doc
    Stack,
    /// Doc
    Storage,
}

/// Doc
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MemoryOp {
    rw: RW,
    gc: GlobalCounter,
    addr: MemoryAddress,
    value: EvmWord,
}

impl MemoryOp {
    pub const fn new(rw: RW, gc: GlobalCounter, addr: MemoryAddress, value: EvmWord) -> MemoryOp {
        MemoryOp {
            rw,
            gc,
            addr,
            value,
        }
    }

    pub const fn rw(&self) -> RW {
        self.rw
    }

    pub const fn target(&self) -> Target {
        Target::Memory
    }

    pub const fn gc(&self) -> GlobalCounter {
        self.gc
    }

    pub const fn address(&self) -> &MemoryAddress {
        &self.addr
    }

    pub const fn value(&self) -> &EvmWord {
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
        match self.address().cmp(other.address()) {
            Ordering::Equal => self.gc().cmp(&other.gc()),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl TryFrom<Operation> for MemoryOp {
    type Error = Error;

    fn try_from(op: Operation) -> Result<Self, Self::Error> {
        match op {
            Operation::Memory(memory_op) => Ok(memory_op),
            _ => Err(Error::InvalidOpConversion),
        }
    }
}

/// Doc
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StackOp {
    rw: RW,
    gc: GlobalCounter,
    addr: StackAddress,
    value: EvmWord,
}

impl StackOp {
    pub const fn new(rw: RW, gc: GlobalCounter, addr: StackAddress, value: EvmWord) -> StackOp {
        StackOp {
            rw,
            gc,
            addr,
            value,
        }
    }

    pub const fn rw(&self) -> RW {
        self.rw
    }

    pub const fn target(&self) -> Target {
        Target::Stack
    }

    pub const fn gc(&self) -> GlobalCounter {
        self.gc
    }

    pub const fn address(&self) -> &StackAddress {
        &self.addr
    }

    pub const fn value(&self) -> &EvmWord {
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
        match self.address().cmp(other.address()) {
            Ordering::Equal => self.gc().cmp(&other.gc()),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl TryFrom<Operation> for StackOp {
    type Error = Error;

    fn try_from(op: Operation) -> Result<Self, Self::Error> {
        match op {
            Operation::Stack(stack_op) => Ok(stack_op),
            _ => Err(Error::InvalidOpConversion),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// Doc
pub(crate) struct StorageOp; // Update with https://hackmd.io/kON1GVL6QOC6t5tf_OTuKA with Han's review

impl TryFrom<Operation> for StorageOp {
    type Error = Error;

    fn try_from(op: Operation) -> Result<Self, Self::Error> {
        match op {
            Operation::Storage(storage_op) => Ok(storage_op),
            _ => Err(Error::InvalidOpConversion),
        }
    }
}

/// Doc
#[derive(Debug, Clone)]
pub(crate) enum Operation {
    /// Doc
    Stack(StackOp),
    /// Doc
    Memory(MemoryOp),
    /// Doc
    Storage(StorageOp),
}

impl From<&StackOp> for Operation {
    fn from(op: &StackOp) -> Self {
        Operation::Stack(op.clone())
    }
}

impl From<StackOp> for Operation {
    fn from(op: StackOp) -> Self {
        Operation::Stack(op)
    }
}

impl From<&MemoryOp> for Operation {
    fn from(op: &MemoryOp) -> Self {
        Operation::Memory(op.clone())
    }
}

impl From<MemoryOp> for Operation {
    fn from(op: MemoryOp) -> Self {
        Operation::Memory(op)
    }
}

impl From<&StorageOp> for Operation {
    fn from(op: &StorageOp) -> Self {
        Operation::Storage(op.clone())
    }
}

impl From<StorageOp> for Operation {
    fn from(op: StorageOp) -> Self {
        Operation::Storage(op)
    }
}

impl PartialEq for Operation {
    fn eq(&self, other: &Operation) -> bool {
        match (self, other) {
            (Operation::Stack(stack_op_1), Operation::Stack(stack_op_2)) => {
                stack_op_1.eq(stack_op_2)
            }
            (Operation::Memory(memory_op_1), Operation::Memory(memory_op_2)) => {
                memory_op_1.eq(memory_op_2)
            }
            (Operation::Storage(storage_op_1), Operation::Storage(storage_op_2)) => {
                storage_op_1.eq(storage_op_2)
            }
            _ => false,
        }
    }
}

impl Eq for Operation {}

impl PartialOrd for Operation {
    fn partial_cmp(&self, other: &Operation) -> Option<Ordering> {
        match (self, other) {
            (Operation::Stack(stack_op_1), Operation::Stack(stack_op_2)) => {
                stack_op_1.partial_cmp(stack_op_2)
            }
            (Operation::Memory(memory_op_1), Operation::Memory(memory_op_2)) => {
                memory_op_1.partial_cmp(memory_op_2)
            }
            (Operation::Storage(storage_op_1), Operation::Storage(storage_op_2)) => {
                storage_op_1.partial_cmp(storage_op_2)
            }
            _ => None,
        }
    }
}

impl Operation {
    pub const fn target(&self) -> Target {
        match self {
            Operation::Memory(_) => Target::Memory,
            Operation::Stack(_) => Target::Stack,
            Operation::Storage(_) => Target::Storage,
        }
    }

    pub const fn is_stack(&self) -> bool {
        matches!(*self, Operation::Stack(_))
    }

    pub const fn is_memory(&self) -> bool {
        matches!(*self, Operation::Memory(_))
    }

    pub const fn is_storage(&self) -> bool {
        matches!(*self, Operation::Storage(_))
    }

    pub fn into_stack_unchecked(self) -> StackOp {
        match self {
            Operation::Stack(stack_op) => unsafe { std::mem::transmute(stack_op) },
            _ => panic!("Broken Invariant"),
        }
    }

    pub fn into_memory_unchecked(self) -> MemoryOp {
        match self {
            Operation::Memory(memory_op) => unsafe { std::mem::transmute(memory_op) },
            _ => panic!("Broken Invariant"),
        }
    }

    pub fn into_storage_unchecked(self) -> StorageOp {
        match self {
            Operation::Storage(storage_op) => unsafe { std::mem::transmute(storage_op) },
            _ => panic!("Broken Invariant"),
        }
    }
}

#[cfg(test)]
mod operation_tests {
    use super::*;
    use num::BigUint;

    #[test]
    fn unchecked_op_transmutations_are_safe() {
        let stack_op = StackOp::new(
            RW::WRITE,
            GlobalCounter(1usize),
            StackAddress::from(1024),
            EvmWord(BigUint::from(0x40u8)),
        );

        let stack_op_as_operation = Operation::from(stack_op.clone());

        let memory_op = MemoryOp::new(
            RW::WRITE,
            GlobalCounter(1usize),
            MemoryAddress(BigUint::from(0x40u8)),
            EvmWord(BigUint::from(0x40u8)),
        );

        let memory_op_as_operation = Operation::from(memory_op.clone());

        assert_eq!(stack_op, stack_op_as_operation.into_stack_unchecked());
        assert_eq!(memory_op, memory_op_as_operation.into_memory_unchecked())
    }
}
