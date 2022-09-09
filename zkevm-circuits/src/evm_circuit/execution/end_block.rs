use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{constraint_builder::ConstraintBuilder, CachedRegion, Cell},
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{CallContextFieldTag, TxContextFieldTag},
};
use eth_types::Field;
use gadgets::util::not;
use halo2_proofs::plonk::Error;

use std::marker::PhantomData;

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
        let rw_counter = cb.curr.state.rw_counter;
        let q_step_last = cb.curr.q_step_last;

        cb.condition(q_step_last.expr(), |cb| {
            // 1. Verify rw_counter counts to the same number of meaningful rows in
            // rw_table to ensure there is no malicious insertion.

            // extra 1 from the tx_id lookup
            let total_rw = rw_counter.expr() + 1.expr();

            // Verify that there are at most total_rw meaningful entries in
            // the rw_table.
            cb.rw_table_start_lookup(1.expr());
            cb.rw_table_start_lookup(MAX_RWS - total_rw);
            // Since every lookup done in the EVM circuit must succeed and uses
            // a unique rw_counter, we know that at least there are
            // total_rw meaningful entries in the rw_table.
            // We conclude that the number of meaningful entries in the rw_table
            // is total_rw.

            // 2. Verify that final step as tx_id identical to the number of
            // txs in tx_table.
            cb.call_context_lookup(
                0.expr(),
                cb.curr.state.call_id.expr(),
                CallContextFieldTag::TxId,
                total_txs,
            );
            // Verify that there are at most total_txs meaningful entries in
            // the tx_table
            cb.tx_context_lookup(1.expr(), TxContextFieldTag::Pad, None, 0.expr());
            cb.tx_context_lookup(
                (MAX_TXS.expr() - total_txs) * TxContextFieldTag::TxSignHash,
                TxContextFieldTag::Pad,
                None,
                0.expr(),
            );
            // instruction.tx_context_lookup(FQ(1),
            // TxContextFieldTag.Pad) instruction.tx_context_lookup(
            //     FQ((tx_table_max_txs - total_tx.expr().n) *
            // TxContextFieldTag.TxSignHash),     TxContextFieldTag.
            // Pad, )
            // # Since every tx lookup done in the EVM circuit must succeed and
            // uses a unique # tx_id, we know that at least there
            // are total_tx meaningful txs # in the tx_table.
            // # We conclude that the number of meaningful txs in the tx_table
            // is total_tx.
        });
        cb.condition(not::expr(q_step_last.expr()), |cb| {});

        Self { total_txs }
    }

    fn assign_exec_step(
        &self,
        _region: &mut CachedRegion<'_, '_, F>,
        _offset: usize,
        _: &Block<F>,
        _: &Transaction,
        _: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}
