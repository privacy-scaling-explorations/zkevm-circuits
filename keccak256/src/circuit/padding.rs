use crate::permutation::tables::RangeCheckConfig;
use eth_types::Field;
use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::convert::TryInto;
use std::iter;

const BYTES_LEN_17_WORDS: usize = 136;

// TODO: byteRLC
// TODO: connect_word_builder
#[derive(Debug, Clone)]
pub(crate) struct PaddingConfig<F> {
    q_all: Selector,
    q_middle: Selector,
    q_last: Selector,
    flag_enable: Column<Advice>,
    byte: Column<Advice>,
    input_len: Column<Advice>,
    acc_len: Column<Advice>,
    diff_inv: Column<Advice>,
    diff_is_zero: IsZeroConfig<F>,
    is_pad_zone: Column<Advice>,
    padded_byte: Column<Advice>,
}

impl<F: Field> PaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_all = meta.selector();
        let q_middle = meta.selector();
        let q_last = meta.selector();
        let flag_enable = meta.advice_column();
        let byte = meta.advice_column();
        let input_len = meta.advice_column();
        let acc_len = meta.advice_column();
        let diff_inv = meta.advice_column();
        let is_pad_zone = meta.advice_column();
        let padded_byte = meta.advice_column();
        let one = Expression::Constant(F::one());
        let two_inv = Expression::Constant(F::from(2).invert().unwrap());
        let diff_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_all) * meta.query_advice(flag_enable, Rotation::cur()),
            |meta| {
                meta.query_advice(input_len, Rotation::cur())
                    - meta.query_advice(acc_len, Rotation::cur())
            },
            diff_inv,
        );
        meta.create_gate("all", |meta| {
            let q_all = meta.query_selector(q_all);
            let flag_enable = meta.query_advice(flag_enable, Rotation::cur());
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::next());

            vec![q_all * flag_enable * (is_pad_zone_cur * byte_cur)]
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
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let is_pad_zone_next = meta.query_advice(is_pad_zone, Rotation::next());
            let diff_is_zero_expr = diff_is_zero.clone().is_zero_expression;
            iter::empty()
                .chain(Some(("increase acc_len", acc_len_next - acc_len_cur - one)))
                .chain(Some((
                    "check padded byte",
                    padded_byte_cur
                        - byte_cur
                        - diff_is_zero_expr.clone() * Expression::Constant(F::from(0x80)),
                )))
                .chain(Some((
                    "check pad_zone",
                    is_pad_zone_next - is_pad_zone_cur - diff_is_zero_expr,
                )))
                .map(move |(name, poly)| (name, q_middle.clone() * flag_enable_cur.clone() * poly))
        });
        meta.create_gate("last", |meta| {
            let q_last = meta.query_selector(q_last);
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let input_len_cur = meta.query_advice(input_len, Rotation::cur());
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let one = Expression::Constant(F::one());
            vec![
                q_last
                    * flag_enable_cur
                    * (padded_byte_cur
                        - diff_is_zero.clone().is_zero_expression
                            * Expression::Constant(F::from(0x80))
                        - one),
            ]
        });
        Self {
            q_all,
            q_middle,
            q_last,
            flag_enable,
            byte,
            input_len,
            acc_len,
            diff_inv,
            diff_is_zero,
            is_pad_zone,
            padded_byte,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        flag_enable: AssignedCell<F, F>,
        acc_len_cell: AssignedCell<F, F>,
        input_len_cell: AssignedCell<F, F>,
        bytes: [u8; BYTES_LEN_17_WORDS],
    ) -> Result<(), Error> {
        let diff_is_zero_chip = IsZeroChip::construct(self.diff_is_zero.clone());
        layouter.assign_region(
            || "padding validation",
            |mut region| {
                let mut acc_len = F::zero();
                let mut is_pad_zone = F::zero();
                for offset in 0..BYTES_LEN_17_WORDS {
                    flag_enable.clone().copy_advice(
                        || "flag enable",
                        &mut region,
                        self.flag_enable,
                        offset,
                    )?;
                    acc_len = {
                        if offset == 0 {
                            acc_len_cell.copy_advice(
                                || "acc_len_first",
                                &mut region,
                                self.acc_len,
                                offset,
                            )?;
                            acc_len_cell.value().cloned().unwrap_or_default()
                        } else {
                            region.assign_advice(
                                || "acc_len_rest",
                                self.acc_len,
                                offset,
                                || Ok(acc_len),
                            )?;
                            acc_len.add(F::one())
                        }
                    };
                    let diff_value = Some(
                        input_len_cell.value().cloned().unwrap_or_default()
                            - acc_len_cell.value().cloned().unwrap_or_default(),
                    );
                    let is_zero = diff_value
                        .map(|diff_value| F::from(diff_value == F::zero()))
                        .unwrap_or_default();
                    diff_is_zero_chip.assign(&mut region, offset, diff_value)?;

                    input_len_cell.copy_advice(
                        || "input len",
                        &mut region,
                        self.input_len,
                        offset,
                    )?;
                    let byte = F::from(bytes[offset] as u64);
                    region.assign_advice(|| "byte", self.byte, offset, || Ok(byte))?;
                    is_pad_zone += is_zero;
                    region.assign_advice(
                        || "is pad zone",
                        self.is_pad_zone,
                        offset,
                        || Ok(is_pad_zone),
                    )?;
                    region.assign_advice(
                        || "padded byte",
                        self.padded_byte,
                        offset,
                        || {
                            Ok(byte
                                // pad head
                                + is_zero * F::from(0x80)
                                // pad tail
                                + F::from(offset == BYTES_LEN_17_WORDS - 1))
                        },
                    )?;
                }

                Ok(())
            },
        )
    }
}
