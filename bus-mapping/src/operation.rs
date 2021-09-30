//! Collection of structs and functions used to:
//! - Define the internals of a [`MemoryOp`], [`StackOp`] and [`StorageOp`].
//! - Define the actual operation types and a wrapper over them (the
//!   [`Operation`] enum).
//! - Define structures that interact with operations such as
//!   [`OperationContainer`].
pub(crate) mod container;

pub use super::evm::{EvmWord, GlobalCounter, MemoryAddress, StackAddress};
use crate::error::Error;
pub use container::OperationContainer;
use core::cmp::Ordering;
use core::fmt::Debug;
use std::convert::TryFrom;

/// Marker that defines whether an Operation performs a `READ` or a `WRITE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RW {
    /// Marks op as READ.
    READ,
    /// Marks op as WRITE.
    WRITE,
}

impl RW {
    /// Returns true if the RW corresponds internally to a [`READ`](RW::READ).
    pub const fn is_read(&self) -> bool {
        match self {
            RW::READ => true,
            RW::WRITE => false,
        }
    }

    /// Returns true if the RW corresponds internally to a [`WRITE`](RW::WRITE).
    pub const fn is_write(&self) -> bool {
        match self {
            RW::WRITE => true,
            RW::READ => false,
        }
    }
}

/// Enum used to differenciate between EVM Stack, Memory and Storage operations.
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum Target {
    /// Dummy target to pad meaningful targets
    Noop,
    /// Means the target of the operation is the Memory.
    Memory,
    /// Means the target of the operation is the Stack.
    Stack,
    /// Means the target of the operation is the Storage.
    Storage,
}

/// Represents a [`READ`](RW::READ)/[`WRITE`](RW::WRITE) into the memory implied
/// by an specific [`OpcodeId`](crate::evm::opcodes::ids::OpcodeId) of the
/// [`ExecutionTrace`](crate::exec_trace::ExecutionTrace).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryOp {
    rw: RW,
    gc: GlobalCounter,
    addr: MemoryAddress,
    value: u8,
}

impl MemoryOp {
    /// Create a new instance of a `MemoryOp` from it's components.
    pub fn new(
        rw: RW,
        gc: GlobalCounter,
        addr: MemoryAddress,
        value: u8,
    ) -> MemoryOp {
        MemoryOp {
            rw,
            gc,
            addr,
            value,
        }
    }

    /// Returns the internal [`RW`] which says whether the operation corresponds
    /// to a Read or a Write into memory.
    pub const fn rw(&self) -> RW {
        self.rw
    }

    /// Returns the [`Target`] (operation type) of this operation.
    pub const fn target(&self) -> Target {
        Target::Memory
    }

    /// Returns the [`GlobalCounter`] associated to this Operation.
    pub const fn gc(&self) -> GlobalCounter {
        self.gc
    }

    /// Returns the [`MemoryAddress`] associated to this Operation.
    pub const fn address(&self) -> &MemoryAddress {
        &self.addr
    }

    /// Returns the bytes read or written by this operation.
    pub fn value(&self) -> u8 {
        self.value
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

/// Represents a [`READ`](RW::READ)/[`WRITE`](RW::WRITE) into the stack implied
/// by an specific [`OpcodeId`](crate::evm::opcodes::ids::OpcodeId) of the
/// [`ExecutionTrace`](crate::exec_trace::ExecutionTrace).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackOp {
    rw: RW,
    gc: GlobalCounter,
    addr: StackAddress,
    value: EvmWord,
}

impl StackOp {
    /// Create a new instance of a `MemoryOp` from it's components.
    pub const fn new(
        rw: RW,
        gc: GlobalCounter,
        addr: StackAddress,
        value: EvmWord,
    ) -> StackOp {
        StackOp {
            rw,
            gc,
            addr,
            value,
        }
    }

    /// Returns the internal [`RW`] which says whether the operation corresponds
    /// to a Read or a Write into memory.
    pub const fn rw(&self) -> RW {
        self.rw
    }

    /// Returns the [`Target`] (operation type) of this operation.
    pub const fn target(&self) -> Target {
        Target::Stack
    }

    /// Returns the [`GlobalCounter`] associated to this Operation.
    pub const fn gc(&self) -> GlobalCounter {
        self.gc
    }

    /// Returns the [`StackAddress`] associated to this Operation.
    pub const fn address(&self) -> &StackAddress {
        &self.addr
    }

    /// Returns the [`EvmWord`] read or written by this operation.
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

/// Represents a [`READ`](RW::READ)/[`WRITE`](RW::WRITE) into the storage
/// implied by an specific [`OpcodeId`](crate::evm::opcodes::ids::OpcodeId) of
/// the [`ExecutionTrace`](crate::exec_trace::ExecutionTrace).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StorageOp {
    rw: RW,
    gc: GlobalCounter,
    addr: MemoryAddress,
    value: EvmWord,
    value_prev: EvmWord,
    storage_key: EvmWord,
}

impl StorageOp {
    /// Create a new instance of a `StorageOp` from it's components.
    pub const fn new(
        rw: RW,
        gc: GlobalCounter,
        addr: MemoryAddress, // todo: use some other struct?
        value: EvmWord,
        value_prev: EvmWord,
        storage_key: EvmWord,
    ) -> StorageOp {
        StorageOp {
            rw,
            gc,
            addr,
            value,
            value_prev,
            storage_key,
        }
    }

    /// Returns the internal [`RW`] which says whether the operation corresponds
    /// to a Read or a Write into storage.
    pub const fn rw(&self) -> RW {
        self.rw
    }

    /// Returns the [`Target`] (operation type) of this operation.
    pub const fn target(&self) -> Target {
        Target::Storage
    }

    /// Returns the [`GlobalCounter`] associated to this Operation.
    pub const fn gc(&self) -> GlobalCounter {
        self.gc
    }

    /// Returns the [`MemoryAddress`] associated to this Operation.
    pub const fn address(&self) -> &MemoryAddress {
        &self.addr
    }

    /// Returns the [`EvmWord`] read or written by this operation.
    pub const fn value(&self) -> &EvmWord {
        &self.value
    }

    /// Returns the [`EvmWord`] read or written by previous operation.
    pub const fn value_prev(&self) -> &EvmWord {
        &self.value_prev
    }

    /// Returns the underlying value representation.
    pub const fn storage_key(&self) -> &EvmWord {
        &self.storage_key
    }
}

impl PartialOrd for StorageOp {
    fn partial_cmp(&self, other: &StorageOp) -> Option<Ordering> {
        match self.address().partial_cmp(other.address()) {
            None => None,
            Some(ord) => match ord {
                std::cmp::Ordering::Equal => self.gc().partial_cmp(&other.gc()),
                _ => Some(ord),
            },
        }
    }
}

impl Ord for StorageOp {
    fn cmp(&self, other: &StorageOp) -> Ordering {
        match self.address().cmp(other.address()) {
            Ordering::Equal => self.gc().cmp(&other.gc()),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl TryFrom<Operation> for StorageOp {
    type Error = Error;

    fn try_from(op: Operation) -> Result<Self, Self::Error> {
        match op {
            Operation::Storage(storage_op) => Ok(storage_op),
            _ => Err(Error::InvalidOpConversion),
        }
    }
}

/// Generic enum that wraps over all the operation types possible.
/// In particular [`StackOp`], [`MemoryOp`] and [`StorageOp`].
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

impl PartialEq for Operation {
    fn eq(&self, other: &Operation) -> bool {
        match (self, other) {
            (Operation::Stack(stack_op_1), Operation::Stack(stack_op_2)) => {
                stack_op_1.eq(stack_op_2)
            }
            (
                Operation::Memory(memory_op_1),
                Operation::Memory(memory_op_2),
            ) => memory_op_1.eq(memory_op_2),
            (
                Operation::Storage(storage_op_1),
                Operation::Storage(storage_op_2),
            ) => storage_op_1.eq(storage_op_2),
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
            (
                Operation::Memory(memory_op_1),
                Operation::Memory(memory_op_2),
            ) => memory_op_1.partial_cmp(memory_op_2),
            (
                Operation::Storage(storage_op_1),
                Operation::Storage(storage_op_2),
            ) => storage_op_1.partial_cmp(storage_op_2),
            _ => None,
        }
    }
}

impl Operation {
    /// Matches over an `Operation` returning the [`Target`] of the iternal op
    /// it stores inside.
    pub const fn target(&self) -> Target {
        match self {
            Operation::Memory(_) => Target::Memory,
            Operation::Stack(_) => Target::Stack,
            Operation::Storage(_) => Target::Storage,
        }
    }

    /// Returns true if the Operation hold internally is a [`StackOp`].
    pub const fn is_stack(&self) -> bool {
        matches!(*self, Operation::Stack(_))
    }

    /// Returns true if the Operation hold internally is a [`MemoryOp`].
    pub const fn is_memory(&self) -> bool {
        matches!(*self, Operation::Memory(_))
    }

    /// Returns true if the Operation hold internally is a [`StorageOp`].
    pub const fn is_storage(&self) -> bool {
        matches!(*self, Operation::Storage(_))
    }

    /// Transmutes the internal (unlabeled) repr of the operation contained
    /// inside of the enum into a [`StackOp`].
    pub fn into_stack_unchecked(self) -> StackOp {
        match self {
            Operation::Stack(stack_op) => unsafe {
                std::mem::transmute(stack_op)
            },
            _ => panic!("Broken Invariant"),
        }
    }

    /// Transmutes the internal (unlabeled) repr of the operation contained
    /// inside of the enum into a [`MemoryOp`].
    pub fn into_memory_unchecked(self) -> MemoryOp {
        match self {
            Operation::Memory(memory_op) => unsafe {
                std::mem::transmute(memory_op)
            },
            _ => panic!("Broken Invariant"),
        }
    }

    /// Transmutes the internal (unlabeled) repr of the operation contained
    /// inside of the enum into a [`StorageOp`].
    pub fn into_storage_unchecked(self) -> StorageOp {
        match self {
            Operation::Storage(storage_op) => unsafe {
                std::mem::transmute(storage_op)
            },
            _ => panic!("Broken Invariant"),
        }
    }
}

#[cfg(test)]
mod operation_tests {
    use super::*;

    #[test]
    fn unchecked_op_transmutations_are_safe() {
        let stack_op = StackOp::new(
            RW::WRITE,
            GlobalCounter(1usize),
            StackAddress::from(1024),
            EvmWord::from(0x40u8),
        );

        let stack_op_as_operation = Operation::from(stack_op.clone());

        let memory_op = MemoryOp::new(
            RW::WRITE,
            GlobalCounter(1usize),
            MemoryAddress(usize::from(0x40u8)),
            0x40u8,
        );

        let memory_op_as_operation = Operation::from(memory_op.clone());

        assert_eq!(stack_op, stack_op_as_operation.into_stack_unchecked());
        assert_eq!(memory_op, memory_op_as_operation.into_memory_unchecked())
    }
}
