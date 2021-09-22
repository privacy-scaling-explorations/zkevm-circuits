//! Definition of each opcode of the EVM.
pub mod ids;
mod mload;
mod push;
mod stop;
use self::push::Push1;
use crate::{
    exec_trace::ExecutionStep, operation::container::OperationContainer, Error,
};
use core::fmt::Debug;
use ids::OpcodeId;
use mload::Mload;
use stop::Stop;

/// Generic opcode trait which defines the logic of the
/// [`Operation`](crate::operation::Operation) that should be generated for an
/// [`ExecutionStep`](crate::exec_trace::ExecutionStep) depending of the
/// [`OpcodeId`] it contains.
pub trait Opcode: Debug {
    /// Generate the associated [`MemoryOp`](crate::operation::MemoryOp)s,
    /// [`StackOp`](crate::operation::StackOp)s, and
    /// [`StorageOp`](crate::operation::StorageOp)s associated to the Opcode
    /// is implemented for.
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error>;
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
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        match *self {
            OpcodeId::PUSH1 => {
                Push1 {}.gen_associated_ops(exec_step, container, next_steps)
            }
            OpcodeId::MLOAD => {
                Mload {}.gen_associated_ops(exec_step, container, next_steps)
            }
            OpcodeId::STOP => {
                Stop {}.gen_associated_ops(exec_step, container, next_steps)
            }
            _ => unimplemented!(),
        }
    }
}
