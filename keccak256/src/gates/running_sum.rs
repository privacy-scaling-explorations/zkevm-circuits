use crate::arith_helpers::*;
use crate::gates::tables::*;
use halo2::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::iter;
use std::marker::PhantomData;

/// | coef | slice | accumulator |
/// |------|-------|-------------|
/// | 5    | 10**2 |       30500 | (step = 2)
/// | 3    | 10**4 |       30000 |
pub struct RunningSumConfig<F> {
    q_enable: Selector,
    is_final: Selector,
    coef: Column<Advice>,
    slice: Column<Advice>,
    accumulator: Column<Advice>,
    step: u32,
    base: u64,
    _marker: PhantomData<F>,
}
impl<F: FieldExt> RunningSumConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        is_final: Selector,
        coef: Column<Advice>,
        slice: Column<Advice>,
        accumulator: Column<Advice>,
        step: u32,
        base: u64,
    ) -> Self {
        let config = Self {
            q_enable,
            is_final,
            coef,
            slice,
            accumulator,
            step,
            base,
            _marker: PhantomData,
        };
        meta.create_gate("mul", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_final = meta.query_selector(is_final);
            let coef = meta.query_advice(coef, Rotation::cur());
            let slice = meta.query_advice(config.slice, Rotation::cur());
            let acc = meta.query_advice(accumulator, Rotation::cur());
            let next_slice = meta.query_advice(config.slice, Rotation::next());
            let next_acc = meta.query_advice(accumulator, Rotation::next());
            let slice_multiplier =
                Expression::Constant(F::from(u64::pow(base, step)));
            iter::empty()
                .chain(Some((
                    "(not final) check next acc",
                    (is_final.clone() - Expression::Constant(F::one()))
                        * (next_acc
                            - (acc.clone() - coef.clone() * slice.clone())),
                )))
                .chain(Some((
                    "(final) check acc",
                    is_final * (acc - coef * slice.clone()),
                )))
                .chain(Some((
                    "next slice",
                    next_slice - slice * slice_multiplier,
                )))
                .map(|(name, poly)| (name, q_enable.clone() * poly))
                .collect::<Vec<_>>()
        });
        config
    }
}

pub struct BlockCountAccConfig<F> {
    q_enable: Selector,
    // block count, step 2 acc, step 3 acc
    block_count_cols: [Column<Advice>; 3],
    step: u32,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BlockCountAccConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        block_count_cols: [Column<Advice>; 3],
        step: u32,
    ) -> Self {
        meta.create_gate("accumulate block count", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let block_count =
                meta.query_advice(block_count_cols[0], Rotation::cur());
            let delta_step2 = meta
                .query_advice(block_count_cols[1], Rotation::next())
                - meta.query_advice(block_count_cols[1], Rotation::cur());
            let delta_step3 = meta
                .query_advice(block_count_cols[2], Rotation::next())
                - meta.query_advice(block_count_cols[2], Rotation::cur());

            match step {
                1 => vec![
                    ("block_count = 0", block_count),
                    ("delta_step2 = 0", delta_step2),
                    ("delta_step3 = 0", delta_step3),
                ],
                2 => vec![
                    ("delta_step2 = block_count", delta_step2 - block_count),
                    ("delta_step3 = 0", delta_step3),
                ],
                3 => vec![
                    ("delta_step2 = 0", delta_step2),
                    ("delta_step3 = block_count", delta_step3 - block_count),
                ],
                _ => {
                    unreachable!("expect step < 4");
                }
            }
            .iter()
            .map(|(name, poly)| (*name, q_enable.clone() * poly.clone()))
            .collect::<Vec<_>>()
        });

        Self {
            q_enable,
            block_count_cols,
            step,
            _marker: PhantomData,
        }
    }
}

pub struct BlockCountFinalConfig<F> {
    q_enable: Selector,
    block_count_cols: [Column<Advice>; 3],
    _marker: PhantomData<F>,
}
impl<F: FieldExt> BlockCountFinalConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        block_count_cols: [Column<Advice>; 3],
    ) -> Self {
        meta.create_gate("block count final check", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let step2_acc =
                meta.query_advice(block_count_cols[1], Rotation::cur());
            let step3_acc =
                meta.query_advice(block_count_cols[2], Rotation::cur());
            iter::empty()
                .chain(Some((
                    "step2_acc <=12",
                    (0..=12)
                        .map(|x| {
                            step2_acc.clone() - Expression::Constant(F::from(x))
                        })
                        .reduce(|a, b| a * b),
                )))
                .chain(Some((
                    "step3_acc <= 13 * 13",
                    (0..=13 * 13)
                        .map(|x| {
                            step3_acc.clone() - Expression::Constant(F::from(x))
                        })
                        .reduce(|a, b| a * b),
                )))
                .map(|(name, poly)| match poly {
                    Some(poly) => (name, q_enable.clone() * poly),
                    None => (name, Expression::Constant(F::zero())),
                })
                .collect::<Vec<_>>()
        });

        Self {
            q_enable,
            block_count_cols,
            _marker: PhantomData,
        }
    }
}

pub struct RotateConversionConfig<F> {
    q_enable: Selector,
    // coef, slice, acc
    base_13_cols: [Column<Advice>; 3],
    // coef, slice, acc
    base_9_cols: [Column<Advice>; 3],
    // block count, step 2 acc, step 3 acc
    block_count_cols: [Column<Advice>; 3],
    base_13_to_base_9_lookup: Base13toBase9TableConfig<F>,
    b13_rs_config: RunningSumConfig<F>,
    b9_rs_config: RunningSumConfig<F>,
    block_count_acc_config: BlockCountAccConfig<F>,
}

impl<F: FieldExt> RotateConversionConfig<F> {
    pub fn configure(
        q_enable: Selector,
        is_final: Selector,
        meta: &mut ConstraintSystem<F>,
        base_13_cols: [Column<Advice>; 3],
        base_9_cols: [Column<Advice>; 3],
        block_count_cols: [Column<Advice>; 3],
        step: u32,
    ) -> Self {
        let base_13_to_base_9_lookup = Base13toBase9TableConfig::configure(
            meta,
            q_enable,
            base_13_cols[1],
            base_9_cols[1],
            block_count_cols[0],
        );

        let b13_rs_config = RunningSumConfig::configure(
            meta,
            q_enable,
            is_final,
            base_13_cols[0],
            base_13_cols[1],
            base_13_cols[2],
            step,
            B13,
        );

        let b9_rs_config = RunningSumConfig::configure(
            meta,
            q_enable,
            is_final,
            base_9_cols[0],
            base_9_cols[1],
            base_9_cols[2],
            step,
            B9,
        );

        let block_count_acc_config = BlockCountAccConfig::configure(
            meta,
            q_enable,
            block_count_cols,
            step,
        );

        Self {
            q_enable,
            base_13_cols,
            base_9_cols,
            block_count_cols,
            base_13_to_base_9_lookup,
            b13_rs_config,
            b9_rs_config,
            block_count_acc_config,
        }
    }
}
