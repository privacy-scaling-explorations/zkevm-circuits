#![allow(missing_docs)]
use gadgets::is_zero::{IsZeroChip, IsZeroConfig};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, VirtualCells},
    poly::Rotation,
};

use crate::{
    evm_circuit::{
        table::LookupTable,
        util::{and, constraint_builder::BaseConstraintBuilder, not, or},
    },
    util::Expr,
};

/// The rw table shared between evm circuit and state circuit
#[derive(Clone, Debug)]
pub struct CopyTable<F> {
    pub q_step: Selector,
    pub q_first: Column<Advice>,
    pub q_last: Column<Advice>,
    pub id: Column<Advice>,
    pub log_id: Column<Advice>,
    pub tag: Column<Advice>,
    pub addr: Column<Advice>,
    pub addr_end: Column<Advice>,
    pub bytes_left: Column<Advice>,
    pub value: Column<Advice>,
    pub is_code: Column<Advice>,
    pub is_pad: Column<Advice>,
    pub rw_counter: Column<Advice>,
    pub rwc_inc_left: Column<Advice>,

    pub is_memory_inv: Column<Advice>,
    pub is_bytecode_inv: Column<Advice>,
    pub is_tx_calldata_inv: Column<Advice>,
    pub is_tx_log_inv: Column<Advice>,

    pub is_memory: IsZeroConfig<F>,
    pub is_bytecode: IsZeroConfig<F>,
    pub is_tx_calldata: IsZeroConfig<F>,
    pub is_tx_log: IsZeroConfig<F>,
}

impl<F: FieldExt> LookupTable<F> for CopyTable<F> {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.q_first, Rotation::cur()),
            meta.query_advice(self.id, Rotation::cur()),
            meta.query_advice(self.tag, Rotation::cur()),
            meta.query_advice(self.id, Rotation::next()),
            meta.query_advice(self.tag, Rotation::next()),
            meta.query_advice(self.addr, Rotation::cur()),
            meta.query_advice(self.addr_end, Rotation::cur()),
            meta.query_advice(self.addr, Rotation::next()),
            meta.query_advice(self.bytes_left, Rotation::cur()),
            meta.query_advice(self.rw_counter, Rotation::cur()),
            meta.query_advice(self.rwc_inc_left, Rotation::cur()),
            meta.query_advice(self.log_id, Rotation::next()),
        ]
    }
}

impl<F: FieldExt> CopyTable<F> {
    pub fn construct(meta: &mut ConstraintSystem<F>, fixed_table: &dyn LookupTable<F>) -> Self {
        let q_step = meta.complex_selector();
        let q_first = meta.advice_column();
        let q_last = meta.advice_column();
        let id = meta.advice_column();
        let log_id = meta.advice_column();
        let tag = meta.advice_column();
        let addr = meta.advice_column();
        let addr_end = meta.advice_column();
        let bytes_left = meta.advice_column();
        let value = meta.advice_column();
        let is_code = meta.advice_column();
        let is_pad = meta.advice_column();
        let rw_counter = meta.advice_column();
        let rwc_inc_left = meta.advice_column();

        let is_memory_inv = meta.advice_column();
        let is_bytecode_inv = meta.advice_column();
        let is_tx_calldata_inv = meta.advice_column();
        let is_tx_log_inv = meta.advice_column();

        let is_memory = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - 1.expr(),
            is_memory_inv,
        );
        let is_bytecode = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - 2.expr(),
            is_memory_inv,
        );
        let is_tx_calldata = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - 3.expr(),
            is_memory_inv,
        );
        let is_tx_log = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - 4.expr(),
            is_memory_inv,
        );

        meta.create_gate("verify row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean("q_step == 0 || q_step == 1", meta.query_selector(q_step));
            cb.require_boolean(
                "q_first == 0 || q_first == 1",
                meta.query_advice(q_first, Rotation::cur()),
            );
            cb.require_boolean(
                "q_last == 0 || q_last == 1",
                meta.query_advice(q_last, Rotation::cur()),
            );
            cb.require_zero(
                "q_first == 0 when q_step == 0",
                and::expr([
                    1.expr() - meta.query_selector(q_step),
                    meta.query_advice(q_first, Rotation::cur()),
                ]),
            );
            cb.require_zero(
                "q_last == 0 when q_step == 1",
                and::expr([
                    meta.query_advice(q_last, Rotation::cur()),
                    meta.query_selector(q_step),
                ]),
            );

            cb.condition(
                not::expr(or::expr([
                    meta.query_advice(q_last, Rotation::cur()),
                    meta.query_advice(q_last, Rotation::next()),
                ])),
                |cb| {
                    cb.require_equal(
                        "rows[0].id == rows[2].id",
                        meta.query_advice(id, Rotation::cur()),
                        meta.query_advice(id, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].log_id == rows[2].log_id",
                        meta.query_advice(log_id, Rotation::cur()),
                        meta.query_advice(log_id, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].tag == rows[2].tag",
                        meta.query_advice(tag, Rotation::cur()),
                        meta.query_advice(tag, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].addr + 1 == rows[2].addr",
                        meta.query_advice(addr, Rotation::cur()) + 1.expr(),
                        meta.query_advice(addr, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].addr_end == rows[2].addr_end",
                        meta.query_advice(addr_end, Rotation::cur()),
                        meta.query_advice(addr_end, Rotation(2)),
                    );
                },
            );

            let rw_diff = and::expr([
                not::expr(meta.query_advice(is_pad, Rotation::cur())),
                not::expr(is_memory.is_zero_expression.clone())
                    + not::expr(is_tx_log.is_zero_expression.clone()),
            ]);
            cb.condition(
                not::expr(meta.query_advice(q_last, Rotation::cur())),
                |cb| {
                    cb.require_equal(
                        "rows[0].rw_counter + rw_diff == rows[1].rw_counter",
                        meta.query_advice(rw_counter, Rotation::cur()) + rw_diff.clone(),
                        meta.query_advice(rw_counter, Rotation::next()),
                    );
                    cb.require_equal(
                        "rows[0].rwc_inc_left - rw_diff == rows[1].rwc_inc_left",
                        meta.query_advice(rwc_inc_left, Rotation::cur()) - rw_diff.clone(),
                        meta.query_advice(rwc_inc_left, Rotation::next()),
                    );
                },
            );
            cb.condition(meta.query_advice(q_last, Rotation::cur()), |cb| {
                cb.require_equal(
                    "rwc_inc_left == 1 for last row in the copy slot",
                    meta.query_advice(rwc_inc_left, Rotation::cur()),
                    rw_diff,
                );
            });

            cb.gate(not::expr(meta.query_advice(is_pad, Rotation::cur())))
        });

        meta.create_gate("verify step", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "bytes_left == 1 for last step",
                and::expr([
                    meta.query_advice(q_last, Rotation::next()),
                    1.expr() - meta.query_advice(bytes_left, Rotation::cur()),
                ]),
            );
            cb.require_zero(
                "bytes_left == bytes_left_next + 1 for non-last step",
                and::expr([
                    1.expr() - meta.query_advice(q_last, Rotation::next()),
                    meta.query_advice(bytes_left, Rotation::cur())
                        - meta.query_advice(bytes_left, Rotation(2))
                        - 1.expr(),
                ]),
            );
            cb.require_equal(
                "write value == read value",
                meta.query_advice(value, Rotation::cur()),
                meta.query_advice(value, Rotation::next()),
            );
            cb.require_zero(
                "value == 0 when is_pad == 1 for read",
                and::expr([
                    meta.query_advice(is_pad, Rotation::cur()),
                    meta.query_advice(value, Rotation::cur()),
                ]),
            );

            // TODO(rohit): is_pad == 1 - (src_addr < src_addr_end) for read row
            // Need the LtGadget for this.

            cb.require_zero(
                "is_pad == 0 for write row",
                meta.query_advice(is_pad, Rotation::next()),
            );

            cb.gate(meta.query_selector(q_step))
        });

        // TODO(rohit): fixed lookup to copy pairs.

        Self {
            q_step,
            q_first,
            q_last,
            id,
            log_id,
            tag,
            addr,
            addr_end,
            bytes_left,
            value,
            is_code,
            is_pad,
            rw_counter,
            rwc_inc_left,

            is_memory_inv,
            is_bytecode_inv,
            is_tx_calldata_inv,
            is_tx_log_inv,

            is_memory,
            is_bytecode,
            is_tx_calldata,
            is_tx_log,
        }
    }
}
