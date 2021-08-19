pub(crate) mod exec_step;
use crate::evm::EvmWord;
use crate::operation::{container::OperationContainer, Operation};
use core::ops::{Index, IndexMut};
pub(crate) use exec_step::ExecutionStep;
use pasta_curves::arithmetic::FieldExt;

/// Doc
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExecutionTrace<F: FieldExt> {
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
    fn container_mut(&mut self) -> &mut OperationContainer {
        &mut self.container
    }

    // Generates the trace setting the propper GC's and BusMappings for each step.
    pub fn new(mut entries: Vec<ExecutionStep>, block_ctants: BlockConstants<F>) -> Self {
        let mut container = OperationContainer::new();
        let mut gc_counter = 0usize;

        entries.iter_mut().for_each(|exec_step| {
            exec_step.set_gc(gc_counter);
            gc_counter += exec_step.gen_associated_ops::<F>(&mut container);
            // Sum 1 to counter so that we set the next exec_step GC to the correct index
            gc_counter += 1;
        });

        ExecutionTrace {
            entries,
            block_ctants,
            container,
        }
    }

    pub fn add_op_to_container(&mut self, op: Operation, exec_step_idx: usize) {
        let op_ref = self.container_mut().insert(op);
        self.entries[exec_step_idx]
            .bus_mapping_instances_mut()
            .insert(op_ref);
    }
}

#[cfg(test)]
mod trace_tests {
    use super::*;
    use crate::error::Error;
    use crate::{
        evm::{
            opcodes::ids::OpcodeId, GlobalCounter, Instruction, MemoryAddress, ProgramCounter,
            StackAddress,
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

        let block_ctants = BlockConstants {
            hash: EvmWord(BigUint::from(0u8)),
            coinbase: pasta_curves::Fp::zero(),
            timestamp: pasta_curves::Fp::zero(),
            number: pasta_curves::Fp::zero(),
            difficulty: pasta_curves::Fp::zero(),
            gaslimit: pasta_curves::Fp::zero(),
            chain_id: pasta_curves::Fp::zero(),
        };

        // Generate the expected ExecutionTrace corresponding to the JSON provided above.

        // Container is shared across ExecutionSteps
        let mut container = OperationContainer::new();

        // The memory is the same in both steps as none of them touches the memory of the EVM.
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
            Instruction::new(OpcodeId::PUSH1, Some(EvmWord(BigUint::from(0x40u8)))),
            ProgramCounter::from(0),
            GlobalCounter::from(0),
        );

        // Add StackOp associated to this opcode to the container & step.bus_mapping
        step_1.bus_mapping_instances_mut().register_and_insert(
            &mut container,
            StackOp::new(
                RW::WRITE,
                GlobalCounter(1usize),
                StackAddress::from(1024),
                EvmWord(BigUint::from(0x40u8)),
            ),
        );

        // Generate Step2 corresponding to PUSH1 80
        let mut step_2 = ExecutionStep::new(
            mem_map.clone(),
            vec![
                EvmWord(BigUint::from(0x40u8)),
                EvmWord(BigUint::from(0x80u8)),
            ],
            Instruction::new(OpcodeId::PUSH1, Some(EvmWord(BigUint::from(0x80u8)))),
            ProgramCounter::from(1),
            GlobalCounter::from(2),
        );

        // Add StackOp associated to this opcode to the container & step.bus_mapping
        step_2.bus_mapping_instances_mut().register_and_insert(
            &mut container,
            StackOp::new(
                RW::WRITE,
                GlobalCounter(3usize),
                StackAddress::from(1023),
                EvmWord(BigUint::from(0x80u8)),
            ),
        );
        let expected_exec_trace = ExecutionTrace {
            entries: vec![step_1, step_2],
            block_ctants: block_ctants.clone(),
            container,
        };

        // Obtained trace computation
        let trace_loaded: Vec<ExecutionStep> =
            serde_json::from_str::<Vec<ParsedExecutionStep>>(input_trace)
                .expect("Error on parsing")
                .iter()
                .enumerate()
                .map(|(idx, step)| ExecutionStep::try_from((step, GlobalCounter(idx))))
                .collect::<Result<Vec<ExecutionStep>, Error>>()
                .expect("Error on conversion");

        let obtained_exec_trace = ExecutionTrace::new(trace_loaded, block_ctants);

        assert_eq!(obtained_exec_trace, expected_exec_trace)
    }
}
