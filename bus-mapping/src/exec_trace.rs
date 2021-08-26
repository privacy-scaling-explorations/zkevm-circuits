//! This module contains the logic for parsing and interacting with EVM
//! execution traces.
pub(crate) mod exec_step;
use crate::evm::EvmWord;
use crate::operation::Target;
use crate::operation::{container::OperationContainer, Operation};
use core::ops::{Index, IndexMut};
pub use exec_step::ExecutionStep;
use pasta_curves::arithmetic::FieldExt;

/// Definition of all of the constants related to an Ethereum block and
/// therefore, related with an [`ExecutionTrace`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockConstants<F: FieldExt> {
    hash: EvmWord, // Until we know how to deal with it
    coinbase: F,
    timestamp: F,
    number: F,
    difficulty: F,
    gas_limit: F,
    chain_id: F,
    base_fee: F,
}

impl<F: FieldExt> BlockConstants<F> {
    #[allow(clippy::too_many_arguments)]
    /// Generates a new `BlockConstants` instance from it's fields.
    pub fn new(
        hash: EvmWord,
        coinbase: F,
        timestamp: F,
        number: F,
        difficulty: F,
        gas_limit: F,
        chain_id: F,
        base_fee: F,
    ) -> BlockConstants<F> {
        BlockConstants {
            hash,
            coinbase,
            timestamp,
            number,
            difficulty,
            gas_limit,
            chain_id,
            base_fee,
        }
    }
    #[inline]
    /// Return the hash of a block.
    pub fn hash(&self) -> &EvmWord {
        &self.hash
    }

    #[inline]
    /// Return the coinbase of a block.
    pub fn coinbase(&self) -> &F {
        &self.coinbase
    }

    #[inline]
    /// Return the timestamp of a block.
    pub fn timestamp(&self) -> &F {
        &self.timestamp
    }

    #[inline]
    /// Return the block number.
    pub fn number(&self) -> &F {
        &self.number
    }

    #[inline]
    /// Return the difficulty of a block.
    pub fn difficulty(&self) -> &F {
        &self.difficulty
    }

    #[inline]
    /// Return the gas_limit of a block.
    pub fn gas_limit(&self) -> &F {
        &self.gas_limit
    }

    #[inline]
    /// Return the chain ID associated to a block.
    pub fn chain_id(&self) -> &F {
        &self.chain_id
    }

    #[inline]
    /// Return the base fee of a block.
    pub fn base_fee(&self) -> &F {
        &self.base_fee
    }
}

/// Result of the parsing of an EVM execution trace.
/// This structure is the centre of the crate and is intended to be the only
/// entry point to it. The `ExecutionTrace` provides three main actions:
///
/// 1. Generate an `ExecutionTrace` instance by parsing an EVM trace (JSON
/// format for now).
///
/// 2. Generate and provide an iterator over all of the
/// [`Instruction`](crate::evm::Instruction)s of the trace and apply it's
/// respective constraints into a provided a mutable reference to a
/// [`ConstraintSystyem`](halo2::plonk::ConstraintSystem).
///
/// 3. Generate and provide and ordered list of all of the
/// [`StackOp`](crate::operation::StackOp)s,
/// [`MemoryOp`](crate::operation::MemoryOp)s and
/// [`StorageOp`](crate::operation::StorageOp)s that each
/// [`Instruction`](crate::evm::Instruction) that derive from the trace so that
/// the State Proof witnesses are already obtained on a structured manner and
/// ready to be added into the State circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionTrace<F: FieldExt> {
    entries: Vec<ExecutionStep>,
    block_ctants: BlockConstants<F>,
    container: OperationContainer,
}

impl<F: FieldExt> Index<usize> for ExecutionTrace<F> {
    type Output = ExecutionStep;
    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl<F: FieldExt> IndexMut<usize> for ExecutionTrace<F> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

impl<F: FieldExt> ExecutionTrace<F> {
    /// Given a vector of [`ExecutionStep`]s and a [`BlockConstants`] instance,
    /// generate an [`ExecutionTrace`] by:
    ///
    /// 1) Setting the correct [`GlobalCounter`](crate::evm::GlobalCounter) to
    /// each [`ExecutionStep`]. 2) Generating the corresponding
    /// [`Operation`]s, registering them in the container and storing the
    /// [`OperationRef`]s to each one of the generated ops into the
    /// bus-mapping instances of each [`ExecutionStep`].
    pub fn new(
        mut entries: Vec<ExecutionStep>,
        block_ctants: BlockConstants<F>,
    ) -> Self {
        let mut container = OperationContainer::new();
        let mut gc = 0usize;

        entries.iter_mut().for_each(|exec_step| {
            exec_step.set_gc(gc);
            gc += exec_step.gen_associated_ops::<F>(&mut container);
            // Sum 1 to counter so that we set the next exec_step GC to the
            // correct index
            gc += 1;
        });

        ExecutionTrace {
            entries,
            block_ctants,
            container,
        }
    }

    /// Registers an [`Operation`] into the [`OperationContainer`] and then adds
    /// a reference to the stored operation ([`OperationRef`]) inside the
    /// bus-mapping instance of the [`ExecutionStep`] located at `exec_step_idx`
    /// inside the [`ExecutionTrace`].
    pub(crate) fn add_op_to_container(
        &mut self,
        op: Operation,
        exec_step_idx: usize,
    ) {
        let op_ref = self.container_mut().insert(op);
        self.entries[exec_step_idx]
            .bus_mapping_instance_mut()
            .push(op_ref);
    }

    /// Returns a mutable reference to the [`OperationContainer`] instance that
    /// the `ExecutionTrace` holds.
    fn container_mut(&mut self) -> &mut OperationContainer {
        &mut self.container
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// The target and index of an `Operation` in the context of an
/// `ExecutionTrace`.
pub struct OperationRef(Target, usize);

impl From<(Target, usize)> for OperationRef {
    fn from(op_ref_data: (Target, usize)) -> Self {
        match op_ref_data.0 {
            Target::Memory => Self(Target::Memory, op_ref_data.1),
            Target::Stack => Self(Target::Stack, op_ref_data.1),
            Target::Storage => Self(Target::Storage, op_ref_data.1),
        }
    }
}

impl OperationRef {
    /// Return the `OperationRef` as a `usize`.
    pub const fn as_usize(&self) -> usize {
        self.1
    }

    /// Return the [`Target`] op type of the `OperationRef`.
    pub const fn target(&self) -> Target {
        self.0
    }
}

#[cfg(test)]
mod trace_tests {
    use super::*;
    use crate::error::Error;
    use crate::{
        evm::{
            opcodes::ids::OpcodeId, GlobalCounter, Instruction, MemoryAddress,
            ProgramCounter, StackAddress,
        },
        exec_trace::{exec_step::ParsedExecutionStep, ExecutionStep},
        operation::{StackOp, RW},
    };
    use alloc::collections::BTreeMap;
    use num::BigUint;
    use std::convert::TryFrom;

    #[test]
    fn exec_trace_parsing() {
        let input_trace = r#"
        [
            {
                "memory": {
                    "0": "0000000000000000000000000000000000000000000000000000000000000000",
                    "20": "0000000000000000000000000000000000000000000000000000000000000000",
                    "40": "0000000000000000000000000000000000000000000000000000000000000000"
                },
                "stack": [
                    "40"
                ],
                "opcode": "PUSH1 40",
                "pc": 0
            },
            {
                "memory": {
                    "00": "0000000000000000000000000000000000000000000000000000000000000000",
                    "20": "0000000000000000000000000000000000000000000000000000000000000000",
                    "40": "0000000000000000000000000000000000000000000000000000000000000000"
                },
                "stack": [
                    "40",
                    "80"
                ],
                "opcode": "PUSH1 80",
                "pc": 1
            }
        ]
        "#;

        let block_ctants = BlockConstants::new(
            EvmWord(BigUint::from(0u8)),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
        );

        // Generate the expected ExecutionTrace corresponding to the JSON
        // provided above.

        // Container is shared across ExecutionSteps
        let mut container = OperationContainer::new();

        // The memory is the same in both steps as none of them touches the
        // memory of the EVM.
        let mut mem_map = BTreeMap::new();
        mem_map.insert(
            MemoryAddress(BigUint::from(0x00u8)),
            EvmWord(BigUint::from(0u8)),
        );
        mem_map.insert(
            MemoryAddress(BigUint::from(0x20u8)),
            EvmWord(BigUint::from(0u8)),
        );
        mem_map.insert(
            MemoryAddress(BigUint::from(0x40u8)),
            EvmWord(BigUint::from(0u8)),
        );

        // Generate Step1 corresponding to PUSH1 40
        let mut step_1 = ExecutionStep::new(
            mem_map.clone(),
            vec![EvmWord(BigUint::from(0x40u8))],
            Instruction::new(
                OpcodeId::PUSH1,
                Some(EvmWord(BigUint::from(0x40u8))),
            ),
            ProgramCounter::from(0),
            GlobalCounter::from(0),
        );

        // Add StackOp associated to this opcode to the container &
        // step.bus_mapping
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                GlobalCounter(1usize),
                StackAddress::from(1023),
                EvmWord(BigUint::from(0x40u8)),
            )));

        // Generate Step2 corresponding to PUSH1 80
        let mut step_2 = ExecutionStep::new(
            mem_map,
            vec![
                EvmWord(BigUint::from(0x40u8)),
                EvmWord(BigUint::from(0x80u8)),
            ],
            Instruction::new(
                OpcodeId::PUSH1,
                Some(EvmWord(BigUint::from(0x80u8))),
            ),
            ProgramCounter::from(1),
            GlobalCounter::from(2),
        );

        // Add StackOp associated to this opcode to the container &
        // step.bus_mapping
        step_2
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                GlobalCounter(3usize),
                StackAddress::from(1022),
                EvmWord(BigUint::from(0x80u8)),
            )));
        let expected_exec_trace = ExecutionTrace {
            entries: vec![step_1, step_2],
            block_ctants: block_ctants.clone(),
            container,
        };

        // Obtained trace computation
        let trace_loaded =
            serde_json::from_str::<Vec<ParsedExecutionStep>>(input_trace)
                .expect("Error on parsing")
                .iter()
                .enumerate()
                .map(|(idx, step)| {
                    ExecutionStep::try_from((step, GlobalCounter(idx)))
                })
                .collect::<Result<Vec<ExecutionStep>, Error>>()
                .expect("Error on conversion");

        let obtained_exec_trace =
            ExecutionTrace::new(trace_loaded, block_ctants);

        assert_eq!(obtained_exec_trace, expected_exec_trace)
    }
}
