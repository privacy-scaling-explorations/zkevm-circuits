// Port this to a macro if possible to avoid defining all the PushN
use super::Opcode;
use crate::{
    evm::GlobalCounter,
    exec_trace::ExecutionStep,
    operation::{container::OperationContainer, StackOp, RW},
};
use halo2::{arithmetic::FieldExt, plonk::ConstraintSystem};

/// Number of ops that PUSH1 adds to the container & busmapping
const PUSH1_OP_NUM: usize = 1;

/// Structure used to implement [`Opcode`] trait over it corresponding to the
/// `PUSH1 X` [`Instruction`](crate::evm::instruction::Instruction).
#[derive(Debug, Copy, Clone)]
pub(crate) struct Push1;

impl Opcode for Push1 {
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
    ) -> usize {
        let op = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(exec_step.gc().0 + 1),
            exec_step.stack_addr(),
            // TODO: This could be more robust.
            // We should have a way to collect this addr (the parsed one which
            // is not tied to 1024)
            exec_step.stack()[exec_step.stack().len() - 1].clone(),
        );

        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(op));

        PUSH1_OP_NUM
    }

    #[allow(unused_variables)]
    fn add_constraints<F: FieldExt>(
        &self,
        exec_step: &ExecutionStep,
        cs: &mut ConstraintSystem<F>,
    ) {
        unimplemented!()
    }
}
