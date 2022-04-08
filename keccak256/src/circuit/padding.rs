use crate::permutation::tables::RangeCheckConfig;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::convert::TryInto;

#[derive(Debug, Clone)]
pub(crate) struct PaddingConfig<F> {
    q_all: Selector,
    q_middle: Selector,
    q_last: Selector,
    state_tag: Column<Advice>,
    flag_enable: Column<Advice>,
    byte: Column<Advice>,
    input_len: Column<Advice>,
    acc_len: Column<Advice>,
    condition_80_inv: Column<Advice>,
    is_pad_zone: Column<Advice>,
    padded_byte: Column<Advice>,
    byte_RLC: Column<Advice>,
}

impl<F: Field> WordBuilderConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, state_tag: Column<Advice>) {
        let q_all = meta.selector();
        let q_middle = meta.selector();
        let q_last = meta.selector();
        let byte = meta.advice_column();
        let input_len = meta.advice_column();
        let acc_len = meta.advice_column();
        let is_pad_zone = meta.advice_column();
        meta.create_gate("all", |meta| {
            let q_all = meta.query_selector(q_all);
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::next());
            let input_len_cur = meta.query_advice(input_len, Rotation::cur());
            let input_len_next = meta.query_advice(input_len, Rotation::next());

            vec![
                q_all.clone() * (is_pad_zone_cur * byte_cur),
                q_all * (input_len_next - input_len_cur),
            ]
        });

        meta.create_gate("middle", |meta| {
            let q_middle = meta.query_selector(q_middle);
            let acc_len_cur = meta.query_advice(acc_len, Rotation::cur());
            let acc_len_next = meta.query_advice(acc_len, Rotation::next());
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());
            let input_len_cur = meta.query_advice(input_len, Rotation::cur());
            let condition_80_inv_cur = meta.query_advice(condition_80_inv, Rotation::cur());
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let is_pad_zone_next = meta.query_advice(is_pad_zone, Rotation::next());
            let one = Expression::Constant(F::one());
            let pad_zone_start = one - (input_len_cur - acc_len_cur) * condition_80_inv_cur;
            vec![
                q_middle.clone() * (acc_len_next - acc_len_cur.clone() - one.clone()),
                q_middle.clone()
                    * (padded_byte_cur
                        - byte_cur
                        - pad_zone_start * Expression::Constant(F::from(0x80))),
                q_middle * (is_pad_zone_next - is_pad_zone_cur - pad_zone_start),
            ]
        });
        meta.create_gate("last", |meta| {
            let q_last = meta.query_selector(q_last);
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());
            let one = Expression::Constant(F::one());
            let pad_zone_start = one.clone() - (input_len_cur - acc_len_cur) * condition_80_inv_cur;
            vec![
                q_last
                    * (padded_byte_cur
                        - byte_cur
                        - pad_zone_start * Expression::Constant(F::from(0x80))
                        - one),
            ]
        });
    }
}
