// Doc this

use crate::evm::{
    EvmWord, GlobalCounter, Instruction, MemoryAddress, ProgramCounter, StackAddress, MEM_ADDR_ZERO,
};
use crate::{error::Error, evm::opcodes::Opcode, operation::container::OperationContainer};
use alloc::collections::BTreeMap;
use core::{convert::TryFrom, str::FromStr};
use halo2::arithmetic::FieldExt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use super::OperationRef;

/// Doc
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExecutionStep {
    memory: BTreeMap<MemoryAddress, EvmWord>,
    stack: Vec<EvmWord>,
    instruction: Instruction,
    pc: ProgramCounter,
    gc: GlobalCounter,
    // Holds refs to the container with the related mem ops.
    bus_mapping_instances: Vec<OperationRef>,
}

impl ExecutionStep {
    /// Doc
    pub fn new(
        memory: BTreeMap<MemoryAddress, EvmWord>,
        stack: Vec<EvmWord>,
        instruction: Instruction,
        pc: ProgramCounter,
        gc: GlobalCounter,
    ) -> Self {
        ExecutionStep {
            memory,
            stack,
            instruction,
            pc,
            gc,
            bus_mapping_instances: Vec::new(),
        }
    }

    pub const fn memory(&self) -> &BTreeMap<MemoryAddress, EvmWord> {
        &self.memory
    }

    pub const fn stack(&self) -> &Vec<EvmWord> {
        &self.stack
    }

    pub fn stack_addr(&self) -> StackAddress {
        // Stack has 1024 slots.
        // First allocation slot for us in the stack is 1023.
        StackAddress::from(1024 - self.stack.len())
    }

    pub fn memory_addr(&self) -> &MemoryAddress {
        self.memory
            .iter()
            .last()
            .map(|items| items.0)
            .unwrap_or_else(|| &MEM_ADDR_ZERO)
    }

    pub const fn instruction(&self) -> &Instruction {
        &self.instruction
    }

    pub const fn pc(&self) -> ProgramCounter {
        self.pc
    }

    pub const fn gc(&self) -> GlobalCounter {
        self.gc
    }

    pub fn set_gc(&mut self, gc: impl Into<GlobalCounter>) {
        self.gc = gc.into()
    }

    pub const fn bus_mapping_instances(&self) -> &Vec<OperationRef> {
        &self.bus_mapping_instances
    }

    pub fn bus_mapping_instances_mut(&mut self) -> &mut Vec<OperationRef> {
        &mut self.bus_mapping_instances
    }

    // Returns the # operations added by the opcode
    pub fn gen_associated_ops<F: FieldExt>(&mut self, container: &mut OperationContainer) -> usize {
        self.instruction()
            .opcode_id()
            .gen_associated_ops(self, container)
    }
}

impl<'a> TryFrom<(&ParsedExecutionStep<'a>, GlobalCounter)> for ExecutionStep {
    type Error = Error;

    fn try_from(
        parse_info: (&ParsedExecutionStep<'a>, GlobalCounter),
    ) -> Result<Self, Self::Error> {
        // Memory part
        let mut mem_map = BTreeMap::new();
        parse_info
            .0
            .memory
            .iter()
            .try_for_each(|(mem_addr, word)| {
                mem_map.insert(MemoryAddress::from_str(mem_addr)?, EvmWord::from_str(word)?);
                Ok(())
            })?;

        // Stack part
        let mut stack = vec![];
        parse_info.0.stack.iter().try_for_each(|word| {
            stack.push(EvmWord::from_str(word)?);
            Ok(())
        })?;

        Ok(ExecutionStep::new(
            mem_map,
            stack,
            Instruction::from_str(parse_info.0.opcode)?,
            parse_info.0.pc,
            parse_info.1,
        ))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[doc(hidden)]
pub struct ParsedExecutionStep<'a> {
    memory: HashMap<&'a str, &'a str>,
    stack: Vec<&'a str>,
    opcode: &'a str,
    pc: ProgramCounter,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::evm::opcodes::ids::OpcodeId;
    use num::BigUint;

    #[test]
    fn parse_single_step() {
        let step_json = r#"
        {
            "memory": {
                "0": "0000000000000000000000000000000000000000000000000000000000000000",
                "20": "0000000000000000000000000000000000000000000000000000000000000000",
                "40": "0000000000000000000000000000000000000000000000000000000000000080"
            },
            "stack": [],
            "opcode": "JUMPDEST",
            "pc": 53
        }
        "#;

        let step_loaded: ExecutionStep = ExecutionStep::try_from((
            &serde_json::from_str::<ParsedExecutionStep>(step_json).expect("Error on parsing"),
            GlobalCounter(0usize),
        ))
        .expect("Error on conversion");

        let expected_step = {
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
                EvmWord(BigUint::from(0x80u8)),
            );

            ExecutionStep::new(
                mem_map,
                vec![],
                Instruction::new(OpcodeId::JUMPDEST, None),
                ProgramCounter(53),
                GlobalCounter(0),
            )
        };

        assert_eq!(step_loaded, expected_step)
    }
}
