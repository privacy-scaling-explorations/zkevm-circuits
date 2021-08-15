use super::{Operation, Target};

/// Doc
#[derive(Debug, Clone)]
pub(crate) struct OperationContainer<T: Operation> {
    memory: Vec<T>,
    stack: Vec<T>,
    storage: Vec<T>,
}

impl<T: Operation> OperationContainer<T> {
    pub fn into_inner(&self, target: Target) -> &Vec<T> {
        match target {
            Target::Memory => &self.memory,
            Target::Stack => &self.stack,
            Target::Storage => &self.storage,
        }
    }

    pub fn into_inner_mut(&mut self, target: Target) -> &mut Vec<T> {
        match target {
            Target::Memory => &mut self.memory,
            Target::Stack => &mut self.stack,
            Target::Storage => &mut self.storage,
        }
    }

    pub fn insert(&mut self, op: T) -> &T {
        let target = op.clone().target();
        self.into_inner_mut(target).push(op);
        // The `None` invariant should be impossible to reach
        &self
            .into_inner(target)
            .last()
            .expect("None invariant should be unreachable")
    }

    pub fn sort_sub_container(&mut self, target: Target) {
        self.into_inner_mut(target).sort();
    }
}
