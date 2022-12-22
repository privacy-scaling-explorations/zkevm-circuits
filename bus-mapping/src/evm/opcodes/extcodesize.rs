use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::Opcode;
use crate::operation::{AccountField, CallContextField, TxAccessListAccountOp, RW};
use crate::state_db::Account;
use crate::Error;
use eth_types::{GethExecStep, ToAddress, ToWord, Word, U256};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Extcodesize;

impl Opcode for Extcodesize {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        // Read account address from stack.
        let address = geth_step.stack.last()?.to_address();
        state.stack_read(
            &mut exec_step,
            geth_step.stack.last_filled(),
            address.to_word(),
        )?;

        // Read transaction ID, rw_counter_end_of_reversion, and is_persistent from call
        // context.
        for (field, value) in [
            (CallContextField::TxId, U256::from(state.tx_ctx.id())),
            (
                CallContextField::RwCounterEndOfReversion,
                U256::from(state.call()?.rw_counter_end_of_reversion as u64),
            ),
            (
                CallContextField::IsPersistent,
                U256::from(state.call()?.is_persistent as u64),
            ),
        ] {
            state.call_context_read(&mut exec_step, state.call()?.call_id, field, value);
        }

        // Update transaction access list for account address.
        let is_warm = state.sdb.check_account_in_access_list(&address);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id: state.tx_ctx.id(),
                address,
                is_warm: true,
                is_warm_prev: is_warm,
            },
        )?;

        // Read account code hash and get code length.
        let (exists, &Account { code_hash, .. }) = state.sdb.get_account(&address);
        let code_size = if exists {
            let code_hash_word = code_hash.to_word();
            state.account_read(
                &mut exec_step,
                address,
                AccountField::CodeHash,
                code_hash_word,
                code_hash_word,
            )?;
            state.code(code_hash)?.len()
        } else {
            state.account_read(
                &mut exec_step,
                address,
                AccountField::NonExisting,
                Word::zero(),
                Word::zero(),
            )?;
            0
        };

        // Write the EXTCODESIZE result to stack.
        debug_assert_eq!(code_size, geth_steps[1].stack.last()?.as_usize());
        state.stack_write(
            &mut exec_step,
            geth_steps[1].stack.nth_last_filled(0),
            code_size.into(),
        )?;

        Ok(vec![exec_step])
    }
}
