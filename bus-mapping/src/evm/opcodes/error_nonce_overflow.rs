use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::Opcode;
use crate::operation::{AccountField, CallContextField};
use crate::Error;
use eth_types::{GethExecStep, ToWord};

#[derive(Debug, Copy, Clone)]
pub(crate) struct ErrorNonceOverflow;

impl Opcode for ErrorNonceOverflow {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = geth_steps.get(1);
        exec_step.error = state.get_step_err(geth_step, next_step).unwrap();
        let address = state.call()?.address;
        println!("call!! {:#?}", state.call().unwrap());
        let call = state.parse_call(geth_step)?;
        let current_call = state.call()?.clone();

        let nonce = state.sdb.get_nonce(&address);
        state.account_read(
            &mut exec_step,
            address,
            AccountField::Nonce,
            nonce.to_word(),
            nonce.to_word(),
        );

        state.push_call(call.clone());
        for (field, value) in [
            (CallContextField::LastCalleeId, 0.into()),
            (CallContextField::LastCalleeReturnDataOffset, 0.into()),
            (CallContextField::LastCalleeReturnDataLength, 0.into()),
        ] {
            state.call_context_write(&mut exec_step, current_call.call_id, field, value);
        }
        state.handle_return(geth_step)?;
        // TODO
        /* situation description
        root call is success, first create call is success, second create call is failed
        root call success is because geth_trace.failed = false, which means success

        case 1: no push_call and no restore context
        => unittest will failed, and I dont think this process is correct

        case 2: push_call but no gen_restore_context_ops
        Rw check all pass. contraint check will failed. The failed constraint looks like very naive.
        Besides, I dont think this is the correct process way for remove `gen_restore_context_ops`

        case 3: no push_call, have gen_restore_context_ops
        Because root call is success, it will make `gen_restore_context_ops` failed when calling self.caller() with msg InvalidGethExecTrace("Call stack is empty but call is used")
        gen_restore_context_ops can not handle this logic properly

        case 4: push_call + gen_restore_context_ops
        rwMap check will mismatch. Because PC, GasLeft.... on caller side didn't not update when entering this call.
        Originally it's handled in create.rs opcode.

        Test step: RUST_BACKTRACE=full RUST_TEST_THREADS=1 cargo test --package zkevm-circuits --lib --features test --features warn-unimplemented -- evm_circuit::execution::error_nonce_overflow::test::test_create_nonce_overflow  --nocapture
        */

        // handles all required steps
        println!("reach here 1");
        // state.gen_restore_context_ops(&mut exec_step, geth_steps)?;
        println!("reach here 2");
        // state.handle_return(geth_step)?;
        println!("reach here 3");
        Ok(vec![exec_step])
    }
}
