//! Doc this

use crate::evm::{EvmWord, GasCost, GasInfo, ProgramCounter};
use crate::ExecutionStep;
use crate::Gas;
use crate::{error::Error, evm::OpcodeId};
use core::{convert::TryFrom, str::FromStr};
use serde::{Deserialize, Serialize};

impl<'a> TryFrom<&ParsedExecutionStep<'a>> for ExecutionStep {
    type Error = Error;

    fn try_from(
        parsed_step: &ParsedExecutionStep<'a>,
    ) -> Result<Self, Self::Error> {
        // Memory part
        let mem_map = parsed_step
            .memory
            .iter()
            .map(|word| EvmWord::from_str(word))
            .collect::<Result<Vec<EvmWord>, Error>>()?;
        let mem_map = mem_map
            .iter()
            .flat_map(|word| word.inner())
            .copied()
            .collect();

        // Stack part
        let mut stack = vec![];
        parsed_step.stack.iter().try_for_each(|word| {
            stack.push(EvmWord::from_str(word)?);
            Ok(())
        })?;

        Ok(ExecutionStep::new(
            mem_map,
            stack,
            // Avoid setting values now. This will be done at the end.
            OpcodeId::from_str(parsed_step.op)?,
            GasInfo::new(parsed_step.gas, parsed_step.gas_cost),
            parsed_step.depth,
            parsed_step.pc,
            0.into(),
        ))
    }
}

/// Helper structure whose only purpose is to serve as a De/Serialization
/// derivation guide for the serde Derive macro.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[doc(hidden)]
pub(crate) struct ParsedExecutionStep<'a> {
    pub(crate) pc: ProgramCounter,
    pub(crate) op: &'a str,
    pub(crate) gas: Gas,
    #[serde(alias = "gasCost")]
    pub(crate) gas_cost: GasCost,
    pub(crate) depth: u8,
    pub(crate) stack: Vec<&'a str>,
    pub(crate) memory: Vec<&'a str>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::evm::{opcodes::ids::OpcodeId, GlobalCounter, Memory, Stack};

    #[test]
    fn parse_single_step() {
        let step_json = r#"
        {
            "pc": 5,
            "op": "JUMPDEST",
            "gas": 82,
            "gasCost": 3,
            "depth": 1,
            "stack": [
                "40"
            ],
            "memory": [
              "0000000000000000000000000000000000000000000000000000000000000000",
              "0000000000000000000000000000000000000000000000000000000000000000",
              "0000000000000000000000000000000000000000000000000000000000000080"
            ]
          }
        "#;

        let step_loaded: ExecutionStep = ExecutionStep::try_from(
            &serde_json::from_str::<ParsedExecutionStep>(step_json)
                .expect("Error on parsing"),
        )
        .expect("Error on conversion");

        let expected_step = {
            let mem_map = Memory(
                EvmWord::from(0u8)
                    .inner()
                    .iter()
                    .chain(EvmWord::from(0u8).inner())
                    .chain(EvmWord::from(0x80u8).inner())
                    .copied()
                    .collect(),
            );

            ExecutionStep {
                memory: mem_map,
                stack: Stack(vec![EvmWord::from(0x40u8)]),
                instruction: OpcodeId::JUMPDEST,
                gas_info: GasInfo::new(82, GasCost::from(3u8)),
                depth: 1,
                pc: ProgramCounter(5),
                gc: GlobalCounter(0),
                bus_mapping_instance: vec![],
            }
        };

        assert_eq!(step_loaded, expected_step)
    }
}
