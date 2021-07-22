//! Crate docs

#![cfg_attr(docsrs, feature(doc_cfg))]
// Temporary until we have more of the crate implemented.
#![allow(dead_code)]
// Catch documentation errors caused by code changes.
#![deny(broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::{
    collections::BTreeMap,
    iter::Iterator,
    ops::{Index, IndexMut},
};

use itertools::Itertools;
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

#[derive(Debug, Clone)]
struct BlockConstants<F: FieldExt> {
    hash: [u8; 256], // Until we know how to deal with it
    coinbase: F,
    timestamp: F,
    number: F,
    difficulty: F,
    gaslimit: F,
    chain_id: F,
}

#[derive(Debug, Clone)]
enum RW {
    READ,
    WRITE,
}

/// Doc
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Target {
    /// Doc
    Memory,
    /// Doc
    Stack,
    /// Doc
    Storage,
}

/// Doc
#[derive(Debug, Clone)]
pub struct Operation<F: FieldExt> {
    mem_op: RW,
    target: Target,
    key: usize,
    value: F,
    opcode_info: String,
}

/// Bus Mapping structure
#[derive(Debug, Clone)]
pub struct BusMapping<F: FieldExt> {
    entries: Vec<Operation<F>>,
    block_ctants: BlockConstants<F>,
    // Helper to sort by key groups. We store how many different keys we have when building the Bus Mapping
    mem_ops_sorted: BTreeMap<usize, Vec<Operation<F>>>,
    stack_ops_sorted: BTreeMap<usize, Vec<Operation<F>>>,
    storage_ops_sorted: BTreeMap<usize, Vec<Operation<F>>>,
}

impl<F: FieldExt> Index<usize> for BusMapping<F> {
    type Output = Operation<F>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl<F: FieldExt> IndexMut<usize> for BusMapping<F> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

impl<F: FieldExt> From<(Vec<Operation<F>>, BlockConstants<F>)> for BusMapping<F> {
    fn from(inp: (Vec<Operation<F>>, BlockConstants<F>)) -> Self {
        // Initialize the BTreeMaps with empty vecs for each key group
        let mut mem_ops_sorted = BTreeMap::new();
        let mut stack_ops_sorted = BTreeMap::new();
        let mut storage_ops_sorted = BTreeMap::new();
        inp.0
            .iter()
            .map(|op| op.key)
            .unique()
            .sorted()
            .for_each(|key| {
                mem_ops_sorted.insert(key, vec![]);
                stack_ops_sorted.insert(key, vec![]);
                storage_ops_sorted.insert(key, vec![]);
            });

        // Actually feed the BTreeMaps with the entries
        inp.0
            .iter()
            .filter(|op| op.target == Target::Stack)
            .for_each(|entry| {
                mem_ops_sorted
                    .get_mut(&entry.key)
                    .expect("This invariant should be unreachable")
                    .push(entry.clone())
            });

        // Actually feed the BTreeMaps with the entries
        inp.0
            .iter()
            .filter(|op| op.target == Target::Memory)
            .for_each(|entry| {
                stack_ops_sorted
                    .get_mut(&entry.key)
                    .expect("This invariant should be unreachable")
                    .push(entry.clone())
            });

        // Actually feed the BTreeMaps with the entries
        inp.0
            .iter()
            .filter(|op| op.target == Target::Storage)
            .for_each(|entry| {
                storage_ops_sorted
                    .get_mut(&entry.key)
                    .expect("This invariant should be unreachable")
                    .push(entry.clone())
            });

        Self {
            entries: inp.0,
            block_ctants: inp.1,
            mem_ops_sorted,
            stack_ops_sorted,
            storage_ops_sorted,
        }
    }
}

impl<F: FieldExt> BusMapping<F> {
    /// Docs
    pub fn stack_part(&self) -> impl Iterator<Item = &Operation<F>> {
        // filter out Operation::Stack
        // group by idx first
        // sort idx increasingly
        // sort gc in each group
        self.stack_ops_sorted.values().rev().flatten()
    }

    /// Docs
    pub fn memory_part(&self) -> impl Iterator<Item = &Operation<F>> {
        // filter out Operation::Memory
        // group by address first
        // sort address increasingly
        // sort gc in each group
        self.mem_ops_sorted.values().flatten()
    }

    /// Docs
    pub fn storage_part(&self) -> impl Iterator<Item = &Operation<F>> {
        self.stack_ops_sorted.values().flatten()
    }
}
