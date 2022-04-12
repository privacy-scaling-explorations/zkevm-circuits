use crate::permutation::tables::RangeCheckConfig;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::convert::TryInto;
use std::iter;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub(crate) struct PaddingConfig<F> {
    q_first: Selector,
    q_all: Selector,
    q_middle: Selector,
    q_last: Selector,
    flag_enable: Column<Advice>,
    byte: Column<Advice>,
    input_len: Column<Advice>,
    acc_len: Column<Advice>,
    condition_80_inv: Column<Advice>,
    is_pad_zone: Column<Advice>,
    padded_byte: Column<Advice>,
    byte_RLC: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: Field> PaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_first = meta.selector();
        let q_all = meta.selector();
        let q_middle = meta.selector();
        let q_last = meta.selector();
        let flag_enable = meta.advice_column();
        let byte = meta.advice_column();
        let input_len = meta.advice_column();
        let acc_len = meta.advice_column();
        let condition_80_inv = meta.advice_column();
        let is_pad_zone = meta.advice_column();
        let padded_byte = meta.advice_column();
        let byte_RLC = meta.advice_column();
        let one = Expression::Constant(F::one());
        let two_inv = Expression::Constant(F::from(2).invert().unwrap());
        meta.create_gate("first", |meta| {
            let q_first = meta.query_selector(q_first);
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let flag_enable_next = meta.query_advice(flag_enable, Rotation::next());
            let acc_len_cur = meta.query_advice(acc_len, Rotation::cur());
            let acc_len_next = meta.query_advice(acc_len, Rotation::next());
            vec![
                (
                    "state_tag to flag",
                    q_first.clone()
                        * (flag_enable_next
                            - flag_enable_cur.clone() * (flag_enable_cur - one.clone()) * two_inv),
                ),
                (
                    "perm_count to acc_len",
                    q_first
                        * (acc_len_next
                            - (acc_len_cur - one.clone()) * Expression::Constant(F::from(136))),
                ),
            ]
        });
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
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let flag_enable_next = meta.query_advice(flag_enable, Rotation::next());
            let acc_len_cur = meta.query_advice(acc_len, Rotation::cur());
            let acc_len_next = meta.query_advice(acc_len, Rotation::next());
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());
            let input_len_cur = meta.query_advice(input_len, Rotation::cur());
            let condition_80_inv_cur = meta.query_advice(condition_80_inv, Rotation::cur());
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let is_pad_zone_next = meta.query_advice(is_pad_zone, Rotation::next());
            let pad_zone_start =
                one.clone() - (input_len_cur - acc_len_cur.clone()) * condition_80_inv_cur;
            iter::empty()
                .chain(Some((
                    "copy flag",
                    flag_enable_next - flag_enable_cur.clone(),
                )))
                .chain(Some(("increase acc_len", acc_len_next - acc_len_cur - one)))
                .chain(Some((
                    "check padded byte",
                    padded_byte_cur
                        - byte_cur
                        - pad_zone_start.clone() * Expression::Constant(F::from(0x80)),
                )))
                .chain(Some((
                    "check pad_zone",
                    is_pad_zone_next - is_pad_zone_cur - pad_zone_start,
                )))
                .map(move |(name, poly)| (name, q_middle.clone() * flag_enable_cur.clone() * poly))
        });
        meta.create_gate("last", |meta| {
            let q_last = meta.query_selector(q_last);
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());
            let input_len_cur = meta.query_advice(input_len, Rotation::cur());
            let acc_len_cur = meta.query_advice(acc_len, Rotation::cur());
            let condition_80_inv_cur = meta.query_advice(condition_80_inv, Rotation::cur());
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let one = Expression::Constant(F::one());
            let pad_zone_start = one.clone() - (input_len_cur - acc_len_cur) * condition_80_inv_cur;
            vec![
                q_last
                    * flag_enable_cur
                    * (padded_byte_cur
                        - byte_cur
                        - pad_zone_start * Expression::Constant(F::from(0x80))
                        - one),
            ]
        });
        Self {
            q_first,
            q_all,
            q_middle,
            q_last,
            flag_enable,
            byte,
            input_len,
            acc_len,
            condition_80_inv,
            is_pad_zone,
            padded_byte,
            byte_RLC,
            _marker: PhantomData,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        flag_enable: AssignedCell<F, F>,
        perm_count: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "padding validation",
            |mut region| {
                let mut offset = 0;
                let flag_enable_cell = flag_enable.copy_advice(
                    || "flag enable",
                    &mut region,
                    self.flag_enable,
                    offset,
                )?;
                let perm_count = perm_count.copy_advice(
                    || "permutation count",
                    &mut region,
                    self.acc_len,
                    offset,
                );
                offset += 1;
                let acc_len = for i in 1..136 {
                    offset += 1;
                };

                Ok(flag_enable_cell)
            },
        )
    }
}
