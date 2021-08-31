//! Definition of each opcode of the EVM.
pub mod ids;
mod push;
use self::push::Push1;
use crate::{
    exec_trace::ExecutionStep, operation::container::OperationContainer,
};
use core::fmt::Debug;
use halo2::{arithmetic::FieldExt, plonk::ConstraintSystem};
use ids::OpcodeId;

/// Generic opcode trait which defines the logic of the
/// [`Operation`](crate::operation::Operation) that should be generated for an
/// [`ExecutionStep`](crate::exec_trace::ExecutionStep) depending of the
/// [`OpcodeId`] it contains. And also the generation of the constraints and
/// ZK-Circuit related definitions associated to the opcode itself.
pub trait Opcode: Debug {
    /// Generate the associated [`MemoryOp`](crate::operation::MemoryOp)s,
    /// [`StackOp`](crate::operation::StackOp)s, and
    /// [`StorageOp`](crate::operation::StorageOp)s associated to the Opcode
    /// is implemented for.
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
    ) -> usize;

    /// Generate the constraints associated to an Opcode and add them inside a
    /// [`ConstraintSystem`] instance.
    fn add_constraints<F: FieldExt>(
        &self,
        exec_step: &ExecutionStep,
        cs: &mut ConstraintSystem<F>,
    );
}

// This is implemented for OpcodeId so that we can downcast the responsabilities
// to the specific Opcode structure implementations since OpcodeId is a single
// structure with all the OPCODES stated as associated constants.
// Easier to solve with a macro. But leaving here for now until we refactor in a
// future PR.
impl Opcode for OpcodeId {
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
    ) -> usize {
        match *self {
            OpcodeId::PUSH1 => {
                Push1 {}.gen_associated_ops(exec_step, container)
            }
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
