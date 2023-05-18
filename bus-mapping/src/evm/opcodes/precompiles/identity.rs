use eth_types::GethExecStep;

use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    Error,
};

#[allow(dead_code)]
fn gen_associated_ops(
    _state: &mut CircuitInputStateRef,
    _geth_steps: &[GethExecStep],
) -> Result<Vec<ExecStep>, Error> {
    unimplemented!()
}
