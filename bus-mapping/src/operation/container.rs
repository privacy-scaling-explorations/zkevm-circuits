use super::{MemoryOp, Op, OpEnum, Operation, StackOp, StorageOp, Target};
use crate::exec_trace::OperationRef;
use itertools::Itertools;

/// The `OperationContainer` is meant to store all of the [`Operation`]s that an
/// [`ExecutionTrace`](crate::exec_trace::ExecutionTrace) performs during its
/// execution.
///
/// Once an operation is inserted into the container, it returns an
/// [`OperationRef`] which holds an index to the operation just inserted.
/// These references are stored inside of the bus-mapping instances of each
/// [`ExecutionStep`](crate::exec_trace::ExecutionStep).
///
/// Finally, the container also provides the capability of retrieving all of the
/// `Stack`, `Memory` or `Storage` operations ordered according to the criterias
/// they have specified.
/// That serves as a way to get an input with which is easy to work with in
/// order to construct the State proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperationContainer {
    pub(crate) memory: Vec<Operation<MemoryOp>>,
    pub(crate) stack: Vec<Operation<StackOp>>,
    pub(crate) storage: Vec<Operation<StorageOp>>,
}

impl Default for OperationContainer {
    fn default() -> Self {
        Self::new()
    }
}

// TODO: impl Index for OperationContainer
impl OperationContainer {
    /// Generates a enw instance of an `OperationContainer`.
    pub fn new() -> Self {
        Self {
            memory: Vec::new(),
            stack: Vec::new(),
            storage: Vec::new(),
        }
    }

    /// Inserts an [`Operation`] into the  container returning a lightwheight
    /// reference to it in the form of an [`OperationRef`] which points to the
    /// location of the inserted operation inside the corresponding container vector.
    pub fn insert<T: Op>(&mut self, op: Operation<T>) -> OperationRef {
        let gc = op.gc();
        match op.op.into_enum() {
            OpEnum::Memory(op) => {
                self.memory.push(Operation::new(gc, op));
                OperationRef::from((Target::Memory, self.storage.len()))
            }
            OpEnum::Stack(op) => {
                self.stack.push(Operation::new(gc, op));
                OperationRef::from((Target::Stack, self.memory.len()))
            }
            OpEnum::Storage(op) => {
                self.storage.push(Operation::new(gc, op));
                OperationRef::from((Target::Storage, self.storage.len()))
            }
        }
    }

    /// Returns a sorted vector of all of the [`MemoryOp`]s contained inside of
    /// the container.
    pub fn sorted_memory(&self) -> Vec<Operation<MemoryOp>> {
        self.memory.iter().sorted().cloned().collect()
    }

    /// Returns a sorted vector of all of the [`StackOp`]s contained inside of
    /// the container.
    pub fn sorted_stack(&self) -> Vec<Operation<StackOp>> {
        self.stack.iter().sorted().cloned().collect()
    }

    /// Returns a sorted vector of all of the [`StorageOp`]s contained inside of
    /// the container.
    pub fn sorted_storage(&self) -> Vec<Operation<StorageOp>> {
        self.storage.iter().sorted().cloned().collect()
    }
}
