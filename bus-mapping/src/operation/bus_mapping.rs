use super::{container::OperationContainer, Operation};
use crate::exec_trace::OperationRef;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BusMappingInstance(pub(crate) Vec<OperationRef>);

// XXX: Impl Index for BusMappingInstance

impl BusMappingInstance {
    pub const fn new() -> BusMappingInstance {
        BusMappingInstance(Vec::new())
    }

    pub fn insert(&mut self, op: OperationRef) {
        self.0.push(op)
    }

    pub fn register_and_insert(
        &mut self,
        container: &mut OperationContainer,
        op: impl Into<Operation>,
    ) {
        self.insert(container.insert(op))
    }
}
