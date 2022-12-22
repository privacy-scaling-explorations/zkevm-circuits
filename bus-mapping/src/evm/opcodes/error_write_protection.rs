use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::{Opcode, OpcodeId};
use crate::Error;
use eth_types::{GethExecStep, ToAddress, ToWord, Word};

#[derive(Debug, Copy, Clone)]
pub(crate) struct ErrorWriteProtection;

impl Opcode for ErrorWriteProtection {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = if geth_steps.len() > 1 {
            Some(&geth_steps[1])
        } else {
            None
        };
        exec_step.error = state.get_step_err(geth_step, next_step).unwrap();
        // assert op code can only be JUMP or JUMPI
       assert!([OpcodeId::SSTORE, OpcodeId::CREATE, OpcodeId::CREATE2, OpcodeId::CALL, OpcodeId::SELFDESTRUCT,
        OpcodeId::LOG0,  OpcodeId::LOG1,  OpcodeId::LOG2,  OpcodeId::LOG3,  OpcodeId::LOG4].contains(&geth_step.op) );
        // assert!(geth_step.op == OpcodeId::SSTORE || geth_step.op == OpcodeId::Create ||
        //     geth_step.op ==  || geth_step.op == OpcodeId::Call);
        //     Log, SELFDESTRUCT

        // `IsSuccess` call context operation is added in gen_restore_context_ops
        state.gen_restore_context_ops(&mut exec_step, geth_steps)?;
        state.handle_return(geth_step)?;
        Ok(vec![exec_step])
    }
}
