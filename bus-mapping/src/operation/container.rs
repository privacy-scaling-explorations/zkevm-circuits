use super::{MemoryOp, Operation, OperationRef, StackOp, StorageOp};

/// Doc
pub(crate) struct OperationContainer {
    memory: Vec<MemoryOp>,
    stack: Vec<StackOp>,
    storage: Vec<StorageOp>,
}

impl OperationContainer {
    pub fn new() -> Self {
        Self {
            memory: Vec::<MemoryOp>::new(),
            stack: Vec::<StackOp>::new(),
            storage: Vec::<StorageOp>::new(),
        }
    }

    pub fn insert(&mut self, op: Operation) -> OperationRef {
        match op {
            Operation::Memory(mem_op) => {
                self.memory.push(mem_op);
                self.memory.last().unwrap().into()
            }
            Operation::Stack(stack_op) => {
                self.stack.push(stack_op);
                self.stack.last().unwrap().into()
            }
            Operation::Storage(storage_op) => {
                self.storage.push(storage_op);
                self.storage.last().unwrap().into()
            }
        }
    }

    pub fn sorted_memory(&mut self) -> &Vec<MemoryOp> {
        self.memory.sort();
        &self.memory
    }

    pub fn sorted_stack(&mut self) -> &Vec<StackOp> {
        self.stack.sort();
        &self.stack
    }

    pub fn sorted_storage(&mut self) -> &Vec<StorageOp> {
        self.storage.sort();
        &self.storage
    }
}
