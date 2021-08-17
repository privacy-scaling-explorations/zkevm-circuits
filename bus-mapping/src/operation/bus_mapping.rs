use super::{MemoryOp, Operation, OperationRef, StackOp, StorageOp, Target};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BusMappingInstance<'a> {
    memory: Vec<OperationRef<'a>>,
    stack: Vec<OperationRef<'a>>,
    storage: Vec<OperationRef<'a>>,
}

impl<'a> BusMappingInstance<'a> {
    pub const fn new() -> BusMappingInstance<'a> {
        BusMappingInstance {
            memory: Vec::new(),
            stack: Vec::new(),
            storage: Vec::new(),
        }
    }

    pub fn insert(&mut self, op: OperationRef<'a>) {
        match op {
            OperationRef::Memory(_) => self.memory.push(op),
            OperationRef::Stack(_) => self.stack.push(op),
            OperationRef::Storage(_) => self.storage.push(op),
        }
    }
}
