use super::Opcode;
use crate::{
    exec_trace::ExecutionStep,
    operation::{
        container::OperationContainer, EthAddress, StackOp, StorageOp, RW,
    },
    Error,
};

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::SLOAD`](crate::evm::OpcodeId::SLOAD) `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Sload;

impl Opcode for Sload {
    #[allow(unused_variables)]
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        let gc_idx_start = exec_step.gc().0;
        let mut gc_idx = gc_idx_start;

        // First stack read
        let stack_value_read = exec_step
            .stack()
            .last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_position = exec_step.stack().last_filled();

        // Manage first stack read at latest stack position
        gc_idx += 1;
        exec_step.bus_mapping_instance_mut().push(container.insert(
            StackOp::new(
                RW::READ,
                gc_idx.into(),
                stack_position,
                stack_value_read,
            ),
        ));

        // Storage read
        let storage_value_read =
            *exec_step.storage().get_or_err(&stack_value_read)?;
        gc_idx += 1;
        exec_step.bus_mapping_instance_mut().push(container.insert(
            StorageOp::new(
                RW::READ,
                gc_idx.into(),
                EthAddress([0u8; 20]), // TODO: Fill with the correct value
                stack_value_read,
                storage_value_read,
                storage_value_read,
            ),
        ));

        // First stack write
        gc_idx += 1;
        exec_step.bus_mapping_instance_mut().push(container.insert(
            StackOp::new(
                RW::WRITE,
                gc_idx.into(),
                stack_position,
                storage_value_read,
            ),
        ));

        Ok(gc_idx - gc_idx_start)
    }
}

#[cfg(test)]
mod sload_tests {
    use super::*;
    use crate::{
        evm::{
            EvmWord, GasCost, GasInfo, GlobalCounter, Memory, OpcodeId,
            ProgramCounter, Stack, StackAddress, Storage,
        },
        BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;
    use std::collections::HashMap;
    use std::iter::FromIterator;

    #[test]
    fn sload_opcode_impl() -> Result<(), Error> {
        let trace = r#"
        [
          {
            "pc": 163,
            "op": "SLOAD",
            "gas": 5217,
            "gasCost": 2100,
            "depth": 1,
            "stack": [
              "0x0"
            ],
            "storage": {
              "0000000000000000000000000000000000000000000000000000000000000000": "000000000000000000000000000000000000000000000000000000000000006f"
            }
          },
          {
            "pc": 97,
            "op": "STOP",
            "gas": 0,
            "gasCost": 0,
            "depth": 1,
            "stack": [
              "0x6f"
            ]
          }
        ]
        "#;

        // Obtained trace computation
        let obtained_exec_trace = ExecutionTrace::<Scalar>::from_trace_bytes(
            trace.as_bytes(),
            BlockConstants::default(),
        )
        .unwrap();

        let mut container = OperationContainer::new();

        // Generate Step1 corresponding to SLOAD
        let mut step_1 = ExecutionStep {
            memory: Memory::empty(),
            stack: Stack(vec![EvmWord::from(0x0u32)]),
            storage: Storage::new(HashMap::from_iter([(
                EvmWord::from(0x0u32),
                EvmWord::from(0x6fu32),
            )])),
            instruction: OpcodeId::SLOAD,
            gas_info: GasInfo {
                gas: 5217,
                gas_cost: GasCost::from(2100u64),
            },
            depth: 1u8,
            pc: ProgramCounter::from(163),
            gc: GlobalCounter(0),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the stack pop.
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::READ,
                GlobalCounter(1),
                StackAddress::from(1023),
                EvmWord::from(0x0u32),
            )));
        // Add StorageOp associated to the storage read.
        step_1.bus_mapping_instance_mut().push(container.insert(
            StorageOp::new(
                RW::READ,
                GlobalCounter(2),
                EthAddress([0u8; 20]), // TODO: Fill with the correct value
                EvmWord::from(0x0u32),
                EvmWord::from(0x6fu32),
                EvmWord::from(0x6fu32),
            ),
        ));
        // Add StackOp associated to the stack push.
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                GlobalCounter(3),
                StackAddress::from(1023),
                EvmWord::from(0x6fu32),
            )));

        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        assert_eq!(obtained_exec_trace[0], step_1);
        assert_eq!(obtained_exec_trace.container, container);

        Ok(())
    }
}
