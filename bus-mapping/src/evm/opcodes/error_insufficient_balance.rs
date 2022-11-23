use super::Opcode;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    operation::{AccountField, CallContextField},
    Error,
};
use eth_types::{GethExecStep, ToWord};

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the `OpcodeId::CALL` `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct InsufficientBalance;

impl Opcode for InsufficientBalance {
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

        let args_offset = geth_step.stack.nth_last(3)?.as_usize();
        let args_length = geth_step.stack.nth_last(4)?.as_usize();
        let ret_offset = geth_step.stack.nth_last(5)?.as_usize();
        let ret_length = geth_step.stack.nth_last(6)?.as_usize();

        state.call_expand_memory(args_offset, args_length, ret_offset, ret_length)?;

        let call = state.parse_call(geth_step).unwrap();
        let current_call = state.call()?.clone();

        for i in 0..7 {
            state.stack_read(
                &mut exec_step,
                geth_step.stack.nth_last_filled(i),
                geth_step.stack.nth_last(i)?,
            )?;
        }

        state.stack_write(
            &mut exec_step,
            geth_step.stack.nth_last_filled(6),
            (0u64).into(), // must fail
        )?;

        state.call_context_read(
            &mut exec_step,
            current_call.call_id,
            CallContextField::CalleeAddress,
            current_call.address.to_word(),
        );

        let (_, callee_account) = state.sdb.get_account(&current_call.address);

        state.account_read(
            &mut exec_step,
            current_call.address,
            AccountField::Balance,
            callee_account.balance,
            callee_account.balance,
        )?;

        state.push_call(call);
        //state.gen_restore_context_ops(&mut exec_step, geth_steps)?;
        state.handle_return(geth_step)?;
        Ok(vec![exec_step])
    }
}
