#![allow(missing_docs)]
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, VirtualCells},
    poly::Rotation,
};

use crate::evm_circuit::{table::LookupTable, witness::RwRow};

// q_step: FQ
//     q_first: FQ
//     q_last: FQ
//     id: FQ  # one of call_id, bytecode_hash, tx_id
//     log_id: FQ  # only used in TxLog
//     tag: FQ  # CopyDataTypeTag
//     addr: FQ
//     addr_end: FQ
//     bytes_left: FQ
//     value: FQ
//     is_code: FQ
//     is_pad: FQ
//     rw_counter: FQ
//     rwc_inc_left: FQ
//     is_memory: FQ
//     is_bytecode: FQ
//     is_tx_calldata: FQ
//     is_tx_log: FQ

/// The rw table shared between evm circuit and state circuit
#[derive(Clone, Copy)]
pub struct CopyTable {
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
}

impl<F: FieldExt> LookupTable<F> for CopyTable {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.q_first, Rotation::cur()),
            meta.query_advice(self.id, Rotation::cur()), // src_id
            meta.query_advice(self.tag, Rotation::cur()), // src_type
            meta.query_advice(self.id, Rotation::next()), // dst_id
            meta.query_advice(self.tag, Rotation::next()), // dst_type
            meta.query_advice(self.addr, Rotation::cur()), // src_addr
            meta.query_advice(self.addr_end, Rotation::cur()), // src_addr_end
            meta.query_advice(self.addr, Rotation::next()), // dst_addr
            meta.query_advice(self.bytes_left, Rotation::cur()), // length
            meta.query_advice(self.rw_counter, Rotation::cur()), // rw_counter
            meta.query_advice(self.rwc_inc_left, Rotation::cur()), // rwc_inc
            meta.query_advice(self.log_id, Rotation::next()), // log_id
        ]
    }
}
impl CopyTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            q_step: meta.complex_selector(),
            q_first: meta.advice_column(),
            q_last: meta.advice_column(),
            id: meta.advice_column(),
            log_id: meta.advice_column(),
            tag: meta.advice_column(),
            addr: meta.advice_column(),
            addr_end: meta.advice_column(),
            bytes_left: meta.advice_column(),
            value: meta.advice_column(),
            is_code: meta.advice_column(),
            is_pad: meta.advice_column(),
            rw_counter: meta.advice_column(),
            rwc_inc_left: meta.advice_column(),
        }
    }

    pub fn assign<F: FieldExt>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        //row: &RwRow<F>,
    ) -> Result<(), Error> {
        // for (column, value) in [
        //     (self.rw_counter, row.rw_counter),
        //     (self.is_write, row.is_write),
        //     (self.tag, row.tag),
        //     (self.key1, row.key1),
        //     (self.key2, row.key2),
        //     (self.key3, row.key3),
        //     (self.key4, row.key4),
        //     (self.value, row.value),
        //     (self.value_prev, row.value_prev),
        //     (self.aux1, row.aux1),
        //     (self.aux2, row.aux2),
        // ] {
        //     region.assign_advice(|| "assign rw row on rw table", column, offset, || Ok(value))?;
        // }
        // Ok(())
    }
}
