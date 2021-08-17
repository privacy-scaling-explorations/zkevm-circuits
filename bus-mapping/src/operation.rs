pub mod bus_mapping;
pub mod container;

use super::evm::{EvmWord, GlobalCounter, MemoryAddress, StackAddress};
use core::cmp::Ordering;
use std::{convert::TryInto, fmt::Debug};

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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryOp {
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
        match self.address().partial_cmp(&other.address()) {
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
        match self.address().cmp(&other.address()) {
            Ordering::Equal => self.gc().cmp(&other.gc()),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
        }
    }
}

/// Doc
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackOp {
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
        match self.address().partial_cmp(&other.address()) {
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
        match self.address().cmp(&other.address()) {
            Ordering::Equal => self.gc().cmp(&other.gc()),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// Doc
pub struct StorageOp; // Update with https://hackmd.io/kON1GVL6QOC6t5tf_OTuKA with Han's review

/// Doc
#[derive(Debug, Clone)]
pub enum Operation {
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

impl<'a> From<OperationRef<'a>> for Operation {
    fn from(op: OperationRef<'a>) -> Operation {
        match op {
            OperationRef::Memory(mem_ref) => Operation::Memory(mem_ref.clone()),
            OperationRef::Stack(mem_ref) => Operation::Stack(mem_ref.clone()),
            OperationRef::Storage(mem_ref) => Operation::Storage(mem_ref.clone()),
        }
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
                unimplemented!()
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
                unimplemented!()
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperationRef<'a> {
    Stack(&'a StackOp),
    Memory(&'a MemoryOp),
    Storage(&'a StorageOp),
}

impl<'a> From<&'a StackOp> for OperationRef<'a> {
    fn from(op: &'a StackOp) -> Self {
        OperationRef::Stack(op)
    }
}

impl<'a> From<&'a MemoryOp> for OperationRef<'a> {
    fn from(op: &'a MemoryOp) -> Self {
        OperationRef::Memory(op)
    }
}

impl<'a> From<&'a StorageOp> for OperationRef<'a> {
    fn from(op: &'a StorageOp) -> Self {
        OperationRef::Storage(op)
    }
}
