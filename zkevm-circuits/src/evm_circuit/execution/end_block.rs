use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Same},
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{CallContextFieldTag, TxContextFieldTag},
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{circuit::Value, plonk::Error};

// TODO: Remove MAX_TXS
#[derive(Clone, Debug)]
pub(crate) struct EndBlockGadget<F, const MAX_TXS: usize, const MAX_RWS: usize> {
    total_txs: Cell<F>,
}

impl<F: Field, const MAX_TXS: usize, const MAX_RWS: usize> ExecutionGadget<F>
    for EndBlockGadget<F, MAX_TXS, MAX_RWS>
{
    const NAME: &'static str = "EndBlock";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndBlock;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let total_txs = cb.query_cell();
        let last_rw_counter = cb.curr.state.rw_counter.clone().expr() - 1.expr();

        cb.step_last(|cb| {
            // 1. Verify rw_counter counts to the same number of meaningful rows in
            // rw_table to ensure there is no malicious insertion.

            // extra 1 from the tx_id lookup
            let total_rw = last_rw_counter + 1.expr();

            // Verify that there are at most total_rw meaningful entries in
            // the rw_table.
            cb.rw_table_start_lookup(1.expr());
            cb.rw_table_start_lookup(MAX_RWS.expr() - total_rw);
            // Since every lookup done in the EVM circuit must succeed and uses
            // a unique rw_counter, we know that at least there are
            // total_rw meaningful entries in the rw_table.
            // We conclude that the number of meaningful entries in the rw_table
            // is total_rw.

            // TODO: We need a selector expression to disable this lookup when there are no
            // txs. Otherwise we can't prove 0txs blocks!  How can we build such expression?
            // ideas:
            // - self.curr.state.rw_counter == 0

            // 2. Verify that final step as tx_id identical to the number of
            // txs in tx_table.
            cb.call_context_lookup(0.expr(), None, CallContextFieldTag::TxId, total_txs.expr());
            // Verify that there are at most total_txs meaningful txs in the tx_table, by
            // showing that the Tx following the last processed one has
            // CallerAddress = 0x0 (which means padding tx).
            // TODO: Update specs to follow this approach of padding and num_txs verif.
            cb.tx_context_lookup(
                total_txs.expr() + 1.expr(),
                TxContextFieldTag::CallerAddress,
                None,
                0.expr(),
            );
            // cb.tx_context_lookup(1.expr(), TxContextFieldTag::Pad, None,
            // 0.expr()); cb.tx_context_lookup(
            //     (MAX_TXS.expr() - total_txs.expr()) *
            // (TxContextFieldTag::TxSignHash as u64).expr(),
            //     TxContextFieldTag::Pad,
            //     None,
            //     0.expr(),
            // );
            // Since every tx lookup done in the EVM circuit must succeed and
            // uses a unique tx_id, we know that at least there
            // are total_tx meaningful txs in the tx_table.
            // We conclude that the number of meaningful txs in the tx_table
            // is total_tx.
        });
        cb.not_step_last(|cb| {
            // Propagate rw_counter and call_id all the way down.
            cb.require_step_state_transition(StepStateTransition {
                rw_counter: Same,
                call_id: Same,
                ..StepStateTransition::any()
            });
        });

        Self { total_txs }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        println!("DBG total_txs: {:?}", block.txs.len());
        self.total_txs.assign(
            region,
            offset,
            Value::known(F::from(block.txs.len() as u64)),
        )?;
        Ok(())
    }
}
