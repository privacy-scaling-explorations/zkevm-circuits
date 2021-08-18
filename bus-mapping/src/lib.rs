//! Crate docs

#![cfg_attr(docsrs, feature(doc_cfg))]
// Temporary until we have more of the crate implemented.
#![allow(dead_code)]
// Catch documentation errors caused by code changes.
#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

extern crate alloc;
mod error;
mod evm;
mod operation;

use core::ops::{Index, IndexMut};

use evm::{EvmWord, ExecutionStep};
use operation::container::OperationContainer;
use pasta_curves::arithmetic::FieldExt;

// -------- EVM Circuit
// gc as index of each row corresponds to the state after the opcode is performed
// 1 gc has 1 entry
//`StackElem{key 	val 	stack_op(READ/WRITE) 	gc   OPCODE    CallID(later_future)}`

//------ State Circuit
// Group target (stack or memory)
// Group by key (location in memory/storage)
// Sorty by gc
//`MemoryElem{target 	gc 	val1 	val2 	val3}`

/// Doc
#[derive(Debug, Clone)]
pub(crate) struct BlockConstants<F: FieldExt> {
    hash: EvmWord, // Until we know how to deal with it
    coinbase: F,
    timestamp: F,
    number: F,
    difficulty: F,
    gaslimit: F,
    chain_id: F,
}

/// Doc
pub(crate) struct ExecutionTrace<'a, F: FieldExt> {
    entries: Vec<ExecutionStep<'a>>,
    block_ctants: BlockConstants<F>,
    container: OperationContainer,
}

impl<'a, F: FieldExt> Index<usize> for ExecutionTrace<'a, F> {
    type Output = ExecutionStep<'a>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl<'a, F: FieldExt> IndexMut<usize> for ExecutionTrace<'a, F> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}
