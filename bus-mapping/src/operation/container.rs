use super::{MemoryOp, Operation, StackOp, StorageOp};
use crate::exec_trace::OperationRef;
use itertools::Itertools;
use std::convert::TryInto;

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
pub struct OperationContainer(pub(crate) Vec<Operation>);

impl Default for OperationContainer {
    fn default() -> Self {
        Self::new()
    }
}

// TODO: impl Index for OperationContainer
impl OperationContainer {
    /// Generates a enw instance of an `OperationContainer`.
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Inserts an [`Operation`] into the  container returning a lightwheight
    /// reference to it in the form of an [`OperationRef`] which points to the
    /// location of the inserted operation inside the container.
    pub fn insert(&mut self, op: impl Into<Operation>) -> OperationRef {
        let op = op.into();
        self.0.push(op.clone());
        OperationRef::from((op.target(), self.0.len()))
    }

    /// Given a [`OperationRef`] return the actual [`Operation`] it is refering
    /// to.
    pub(crate) fn fetch_op(&self, reference: OperationRef) -> &Operation {
        self.0.get(reference.as_usize()).expect("it should not be possible to have a ref to a non-existent operation")
    }

    /// Returns a sorted vector of all of the [`MemoryOp`]s contained inside of
    /// the container.
    pub fn sorted_memory(&self) -> Vec<MemoryOp> {
        self.0
            .iter()
            .map(|op| op.clone().try_into())
            .filter(|result| result.is_ok())
            .map(|result| result.unwrap())
            .sorted()
            .collect()
    }

    /// Returns a sorted vector of all of the [`StackOp`]s contained inside of
    /// the container.
    pub fn sorted_stack(&self) -> Vec<StackOp> {
        self.0
            .iter()
            .map(|op| op.clone().try_into())
            .filter(|result| result.is_ok())
            .map(|result| result.unwrap())
            .sorted()
            .collect()
    }

    /// Returns a sorted vector of all of the [`StorageOp`]s contained inside of
    /// the container.
    pub fn sorted_storage(&self) -> Vec<StorageOp> {
        self.0
            .iter()
            .map(|op| op.clone().try_into())
            .filter(|result| result.is_ok())
            .map(|result| result.unwrap())
            .sorted()
            .collect()
    }
}
