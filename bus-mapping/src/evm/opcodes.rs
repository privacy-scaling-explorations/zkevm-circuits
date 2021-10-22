//! Definition of each opcode of the EVM.
mod add;
pub mod ids;
mod mload;
mod push;
mod sload;
mod stop;
use crate::circuit_input_builder::CircuitInputStateRef;
use crate::eth_types::GethExecStep;
use crate::Error;
use core::fmt::Debug;
use ids::OpcodeId;

use self::push::Push1;
use add::Add;
use mload::Mload;
use sload::Sload;
use stop::Stop;

/// Generic opcode trait which defines the logic of the
/// [`Operation`](crate::operation::Operation) that should be generated for an
/// [`ExecStep`](crate::circuit_input_builder::ExecStep) depending of the
/// [`OpcodeId`] it contains.
pub trait Opcode: Debug {
    /// Generate the associated [`MemoryOp`](crate::operation::MemoryOp)s,
    /// [`StackOp`](crate::operation::StackOp)s, and
    /// [`StorageOp`](crate::operation::StorageOp)s associated to the Opcode
    /// is implemented for.
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        next_steps: &[GethExecStep],
    ) -> Result<(), Error>;
}

type FnGenAssociatedOps = fn(
    state: &mut CircuitInputStateRef,
    next_steps: &[GethExecStep],
) -> Result<(), Error>;

impl OpcodeId {
    fn fn_gen_associated_ops(&self) -> FnGenAssociatedOps {
        match *self {
            OpcodeId::MLOAD => Mload::gen_associated_ops,
            OpcodeId::PUSH1 => Push1::gen_associated_ops,
            OpcodeId::SLOAD => Sload::gen_associated_ops,
            OpcodeId::STOP => Stop::gen_associated_ops,
            OpcodeId::ADD => Add::gen_associated_ops,
            _ => unimplemented!(),
        }
    }

    /// Generate the associated operations according to the particular [`OpcodeId`].
    pub fn gen_associated_ops(
        &self,
        state: &mut CircuitInputStateRef,
        next_steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let fn_gen_associated_ops = self.fn_gen_associated_ops();
        fn_gen_associated_ops(state, next_steps)
    }
}
