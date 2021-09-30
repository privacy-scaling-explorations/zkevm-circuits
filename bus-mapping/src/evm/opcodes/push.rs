use core::ops::Deref;
// Port this to a macro if possible to avoid defining all the PushN
use super::Opcode;
use crate::{
    evm::GlobalCounter,
    exec_trace::ExecutionStep,
    operation::{container::OperationContainer, StackOp, RW},
    Error,
};

/// Number of ops that PUSH1 adds to the container & busmapping
const PUSH1_OP_NUM: usize = 1;

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::PUSH1`](crate::evm::OpcodeId::PUSH1) `OpcodeId`.
/// This is responsible of generating all of the associated [`StackOp`]s and place them
/// inside the trace's [`OperationContainer`].
#[derive(Debug, Copy, Clone)]
pub(crate) struct Push1;

impl Opcode for Push1 {
    fn gen_associated_ops(
        &self,
        // Contains the PUSH1 instr
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        // Contains the next step where we can find the value that was pushed.
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        let op = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(exec_step.gc().0 + 1),
            // Get the value and addr from the next step. Being the last position filled with an element in the stack
            next_steps[0].stack().last_filled(),
            next_steps[0]
                .stack()
                .deref()
                .last()
                .cloned()
                .ok_or(Error::InvalidStackPointer)?,
        );

        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(op));

        Ok(PUSH1_OP_NUM)
    }
}

#[cfg(test)]
mod push_tests {
    use super::*;
    use crate::{
        evm::{
            EvmWord, GasCost, GasInfo, Memory, OpcodeId, ProgramCounter, Stack,
            StackAddress,
        },
        BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;

    #[test]
    fn push1_opcode_impl() -> Result<(), Error> {
        let trace = r#"
        [
            {
            "pc": 7,
            "op": "PUSH1",
            "gas": 79,
            "gasCost": 3,
            "depth": 1,
            "stack": [],
            "memory": [
                "0000000000000000000000000000000000000000000000000000000000000000",
                "0000000000000000000000000000000000000000000000000000000000000000",
                "0000000000000000000000000000000000000000000000000000000000000000"
            ]
            },
              {
                "pc": 8,
                "op": "STOP",
                "gas": 76,
                "gasCost": 0,
                "depth": 1,
                "stack": [
                  "80"
                ],
                "memory": [
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000000"
                ]
              }
        ]
        "#;

        // Obtained trace computation
        let obtained_exec_trace = ExecutionTrace::<Scalar>::from_trace_bytes(
            trace.as_bytes(),
            BlockConstants::default(),
        )?;

        let mut container = OperationContainer::new();
        let mut gc = 0usize;

        // The memory is the same in both steps as none of them edits the
        // memory of the EVM.
        let mem_map = Memory(
            EvmWord::from(0u8)
                .inner()
                .iter()
                .chain(EvmWord::from(0u8).inner())
                .chain(EvmWord::from(0u8).inner())
                .copied()
                .collect(),
        );

        // Generate Step1 corresponding to PUSH1 80
        let mut step_1 = ExecutionStep {
            memory: mem_map,
            stack: Stack::empty(),
            instruction: OpcodeId::PUSH1,
            gas_info: GasInfo {
                gas: 79,
                gas_cost: GasCost::from(3u8),
            },
            depth: 1u8,
            pc: ProgramCounter::from(7),
            gc: gc.into(),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        gc += 1;
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                gc.into(),
                StackAddress::from(1023),
                EvmWord::from(0x80u8),
            )));

        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );

        Ok(())
    }
}
