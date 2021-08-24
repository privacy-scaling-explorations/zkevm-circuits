use super::{MemoryOp, Operation, StackOp, StorageOp};
use crate::exec_trace::OperationRef;
use itertools::Itertools;
use std::convert::TryInto;

#[derive(Debug, Clone, PartialEq, Eq)]
/// Doc
pub(crate) struct OperationContainer(pub(crate) Vec<Operation>);

/// TODO: impl Index for OperationContainer

impl OperationContainer {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn insert(&mut self, op: impl Into<Operation>) -> OperationRef {
        let op = op.into();
        self.0.push(op.clone());
        OperationRef::from((op.target(), self.0.len()))
    }

    pub fn sorted_memory(&self) -> Vec<MemoryOp> {
        self.0
            .iter()
            .map(|op| op.clone().try_into())
            .filter(|result| result.is_ok())
            .map(|result| result.unwrap())
            .sorted()
            .collect()
    }

    pub fn sorted_stack(&self) -> Vec<StackOp> {
        self.0
            .iter()
            .map(|op| op.clone().try_into())
            .filter(|result| result.is_ok())
            .map(|result| result.unwrap())
            .sorted()
            .collect()
    }

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
