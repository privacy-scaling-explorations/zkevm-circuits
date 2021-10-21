//! Definition of each opcode of the EVM.
pub mod ids;
mod mload;
mod push;
mod sload;
mod stop;
use self::push::Push1;
use crate::{
    exec_trace::{Context, ExecutionStep},
    Error,
};
use core::fmt::Debug;
use ids::OpcodeId;
use mload::Mload;
use sload::Sload;
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
        ctx: &mut Context,
        exec_step: &mut ExecutionStep,
        next_steps: &[ExecutionStep],
    ) -> Result<(), Error>;
}

// This is implemented for OpcodeId so that we can downcast the responsabilities
// to the specific Opcode structure implementations since OpcodeId is a single
// structure with all the OPCODES stated as associated constants.
// Easier to solve with a macro. But leaving here for now until we refactor in a
// future PR.
impl Opcode for OpcodeId {
    fn gen_associated_ops(
        &self,
        ctx: &mut Context,
        exec_step: &mut ExecutionStep,
        next_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        match *self {
            OpcodeId::PUSH1 => {
                Push1 {}.gen_associated_ops(ctx, exec_step, next_steps)
            }
            OpcodeId::MLOAD => {
                Mload {}.gen_associated_ops(ctx, exec_step, next_steps)
            }
            OpcodeId::SLOAD => {
                Sload {}.gen_associated_ops(ctx, exec_step, next_steps)
            }
            OpcodeId::STOP => {
                Stop {}.gen_associated_ops(ctx, exec_step, next_steps)
            }
            _ => unimplemented!(),
        }
    }
}
