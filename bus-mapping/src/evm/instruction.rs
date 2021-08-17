use crate::{operation::bus_mapping::BusMappingInstance, EvmWord, ExecutionStep};
use core::str::FromStr;
use ff::Field;
use halo2::plonk::ConstraintSystem;

use super::opcodes::{Opcode, OpcodeId};

/// Doc
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Instruction {
    opcode: OpcodeId,
    assoc_value: Option<EvmWord>,
}

impl Instruction {
    pub const fn new(op: OpcodeId, val: Option<EvmWord>) -> Self {
        Instruction {
            opcode: op,
            assoc_value: val,
        }
    }

    pub const fn opcode(&self) -> OpcodeId {
        self.opcode
    }

    pub const fn value(&self) -> Option<&EvmWord> {
        self.assoc_value.as_ref()
    }
}

impl FromStr for Instruction {
    type Err = crate::error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Separate the instruction from the possible Value associated to it.
        let words: Vec<&str> = s.split_whitespace().into_iter().collect();
        // Allocate value
        let val = match words.get(1) {
            Some(val) => Some(EvmWord::from_str(val)?),
            None => None,
        };

        Ok(Instruction::new(OpcodeId::from_str(words[0])?, val))
    }
}
