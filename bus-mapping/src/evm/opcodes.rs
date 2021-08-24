//! Definition of each opcode of the EVM.
pub mod ids;
mod push;
use self::push::Push1;
use crate::{exec_trace::ExecutionStep, operation::container::OperationContainer};
use core::fmt::Debug;
use halo2::{arithmetic::FieldExt, plonk::ConstraintSystem};
use ids::OpcodeId;

pub(crate) trait Opcode: Debug {
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
    ) -> usize;
    fn add_constraints<F: FieldExt>(&self, exec_step: &ExecutionStep, cs: &mut ConstraintSystem<F>);
}

// Easier to solve with a macro. But leaving here for now until we refactor in a future PR.
impl Opcode for OpcodeId {
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
    ) -> usize {
        match *self {
            OpcodeId::PUSH1 => Push1 {}.gen_associated_ops(exec_step, container),
            _ => unimplemented!(),
        }
    }

    fn add_constraints<F: FieldExt>(
        &self,
        exec_step: &ExecutionStep,
        cs: &mut ConstraintSystem<F>,
    ) {
        match *self {
            OpcodeId::PUSH1 => Push1 {}.add_constraints(exec_step, cs),
            _ => unimplemented!(),
        }
    }
}
