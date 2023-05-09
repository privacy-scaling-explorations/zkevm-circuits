use eth_types::GethExecStep;

use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    evm::Opcode,
    Error,
};

#[derive(Clone, Debug)]
pub struct Identity;

impl Opcode for Identity {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        unimplemented!()
    }
}
