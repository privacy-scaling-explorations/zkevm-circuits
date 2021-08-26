use crate::error::Error;

use super::{opcodes::ids::OpcodeId, EvmWord};
use core::str::FromStr;

/// Represents the union between an [`OpcodeId`] and the actual associated value
/// (if it has any).
/// `Instruction`s are the core of the [`ExecutionStep`] as they contain all the
/// key parts related to the witness generation which is delegated to the
/// [`OpcodeId`]s that they contain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Instruction {
    opcode: OpcodeId,
    assoc_value: Option<EvmWord>,
}

impl Instruction {
    /// Generate a new instance of an `Instruction` from it's fields.
    pub const fn new(op: OpcodeId, val: Option<EvmWord>) -> Self {
        Instruction {
            opcode: op,
            assoc_value: val,
        }
    }

    /// Returns the [`OpcodeId`] associated to this instruction.
    pub const fn opcode_id(&self) -> OpcodeId {
        self.opcode
    }

    /// Returns an [`Option`] with a reference to it's associated [`EvmWord`]
    /// (if there's any).
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

        if let Some(word) = words.get(0) {
            Ok(Instruction::new(OpcodeId::from_str(word)?, val))
        } else {
            Err(Error::OpcodeParsing)
        }
    }
}
