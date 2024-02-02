use super::{
    begin_end_tx::{begin_tx, end_tx},
    TxExecSteps,
};
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecState, ExecStep},
    operation::AccountField,
    Error,
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct InvalidTx;

impl TxExecSteps for InvalidTx {
    fn gen_associated_steps(
        state: &mut CircuitInputStateRef,
        _execution_step: ExecState,
    ) -> Result<ExecStep, Error> {
        let mut exec_step = state.new_invalid_tx_step();
        let call = state.call()?.clone();
        let caller = call.caller_address;

        // Start processing the tx
        begin_tx(state, &mut exec_step, &call)?;

        // Read the nonce to prove mismatch
        state.account_read(
            &mut exec_step,
            caller,
            AccountField::Nonce,
            state.sdb.get_account(&caller).1.nonce.into(),
        )?;

        // Read the balance to compare with intrinsic gas cost + value
        state.account_read(
            &mut exec_step,
            caller,
            AccountField::Balance,
            state.sdb.get_account(&caller).1.balance,
        )?;

        // Stop processing the tx
        end_tx(state, &mut exec_step, &call)?;

        Ok(exec_step)
    }
}
