use crate::arith_helpers::*;
use crate::common::ROTATION_CONSTANTS;
use crate::gates::gate_helpers::Lane;
use crate::gates::tables::*;
use halo2::{
    circuit::{Cell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::iter;
use std::marker::PhantomData;

/// | coef | slice | accumulator |
/// |------|-------|-------------|
/// | 5    | 10**2 |       30500 | (step = 2)
/// | 3    | 10**4 |       30000 |
#[derive(Debug)]
// TODO: make STEP and BASE const generics, make `slice` a fixed column.
pub struct RunningSumConfig<F> {
    q_enable: Selector,
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
        cols: [Column<Advice>; 3],
        step: u32,
        base: u64,
    ) -> Self {
        let config = Self {
            q_enable,
            coef: cols[0],
            slice: cols[1],
            accumulator: cols[2],
            step,
            base,
            _marker: PhantomData,
        };
        meta.create_gate("mul", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let coef = meta.query_advice(config.coef, Rotation::cur());
            let slice = meta.query_advice(config.slice, Rotation::cur());
            let acc = meta.query_advice(config.accumulator, Rotation::cur());
            let next_slice = meta.query_advice(config.slice, Rotation::next());
            let next_acc =
                meta.query_advice(config.accumulator, Rotation::next());
            let slice_multiplier =
                Expression::Constant(F::from(u64::pow(base, step)));
            iter::empty()
                .chain(Some((
                    "next_acc === acc - coef * slice",
                    (next_acc - (acc.clone() - coef.clone() * slice.clone())),
                )))
                .chain(Some((
                    "next_slice === slice * slice_multiplier",
                    next_slice - slice * slice_multiplier,
                )))
                .map(|(name, poly)| (name, q_enable.clone() * poly))
                .collect::<Vec<_>>()
        });
        config
    }
}

#[derive(Debug)]
pub struct SpecialChunkConfig<F> {
    q_enable: Selector,
    high_value: Column<Advice>,
    low_value: Column<Advice>,
    keccak_rotation: u32,
    base_13_last_accumulator: Column<Advice>,
    base_9_last_accumulator: Column<Advice>,
    special_chunk_table_config: SpecialChunkTableConfig<F>,
}

impl<F: FieldExt> SpecialChunkConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        base_13_last_accumulator: Column<Advice>,
        base_9_last_accumulator: Column<Advice>,
        keccak_rotation: u32,
    ) -> Self {
        let high_value = meta.advice_column();
        let low_value = meta.advice_column();
        meta.create_gate("validate base_9_last_accumulator", |meta| {
            let base_9_last_accumulator =
                meta.query_advice(base_9_last_accumulator, Rotation::cur());
            let base_13_last_accumulator =
                meta.query_advice(base_13_last_accumulator, Rotation::cur());
            let high_value = meta.query_advice(high_value, Rotation::cur());
            let low_value = meta.query_advice(low_value, Rotation::cur());
            let base_9_slice = high_value.clone() + low_value.clone();
            let base_9_coef = Expression::Constant(F::from_u64(B9).pow(&[
                keccak_rotation as u64,
                0,
                0,
                0,
            ]));
            let pow_of_13 =
                Expression::Constant(F::from_u64(B13).pow(&[64u64, 0, 0, 0]));

            vec![
                (
                    "base_9_acc === (high_value + low_value) * 9**rotation",
                    base_9_last_accumulator - base_9_slice * base_9_coef,
                ),
                (
                    "base_13_acc === high_value * 13**64 + low_value",
                    base_13_last_accumulator - high_value * pow_of_13
                        + low_value,
                ),
            ]
        });
        let special_chunk_table_config =
            SpecialChunkTableConfig::configure(meta, high_value, low_value);
        Self {
            q_enable,
            high_value,
            low_value,
            keccak_rotation,
            base_13_last_accumulator,
            base_9_last_accumulator,
            special_chunk_table_config,
        }
    }
}

#[derive(Debug)]
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
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
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
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        block_count_cells: [(Cell, Cell); 25],
    ) {
    }
}

#[derive(Debug)]
pub struct ChunkRotateConversionConfig<F> {
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

impl<F: FieldExt> ChunkRotateConversionConfig<F> {
    pub fn configure(
        q_enable: Selector,
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
            base_13_cols,
            step,
            B13,
        );

        let b9_rs_config =
            RunningSumConfig::configure(meta, q_enable, base_9_cols, step, B9);

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

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
    ) -> usize {
        self.b13_rs_config.assign_region();
        self.b9_rs_config.assign_region();
        self.block_count_acc_config.assign_region();
    }
}

/// Determine how many chunks in a step.
/// Usually it's a step of 4 chunks, but the number of chunks could be less near
/// the rotation position and the end of the lane. Those are the special chunks
/// we need to take care of.
fn get_step_size(chunk_idx: u32, rotation: u32) -> u32 {
    const BASE_NUM_OF_CHUNKS: u32 = 4;
    const LANE_SIZE: u32 = 64;
    // near the rotation position of the lane
    if chunk_idx < rotation && rotation < chunk_idx + BASE_NUM_OF_CHUNKS {
        return rotation - chunk_idx;
    }
    // near the end of the lane
    if chunk_idx < LANE_SIZE && LANE_SIZE < chunk_idx + BASE_NUM_OF_CHUNKS {
        return LANE_SIZE - chunk_idx;
    }
    BASE_NUM_OF_CHUNKS
}

#[derive(Debug)]
pub struct LaneRotateConversionConfig<F> {
    q_enable: Selector,
    q_is_special: Selector,
    base_13_cols: [Column<Advice>; 3],
    base_9_cols: [Column<Advice>; 3],
    chunk_rotate_convert_configs: Vec<ChunkRotateConversionConfig<F>>,
    special_chunk_config: SpecialChunkConfig<F>,
    block_count_cols: [Column<Advice>; 3],
    lane_xy: (usize, usize),
}

impl<F: FieldExt> LaneRotateConversionConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        lane_xy: (usize, usize),
    ) -> Self {
        let base_13_cols = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let base_9_cols = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let q_is_special = meta.selector();

        let mut chunk_idx = 1;
        let mut chunk_rotate_convert_configs = vec![];
        let rotation = ROTATION_CONSTANTS[lane_xy.0][lane_xy.1];

        while chunk_idx < 64 {
            let step = get_step_size(chunk_idx, rotation);
            let config = ChunkRotateConversionConfig::configure(
                q_enable,
                meta,
                base_13_cols,
                base_9_cols,
                block_count_cols,
                step,
            );
            chunk_idx += step;
            chunk_rotate_convert_configs.push(config);
        }
        let special_chunk_config = SpecialChunkConfig::configure(
            meta,
            q_is_special,
            base_13_cols[2],
            base_9_cols[2],
            rotation,
        );

        Self {
            q_enable,
            q_is_special,
            base_13_cols,
            base_9_cols,
            chunk_rotate_convert_configs,
            special_chunk_config,
            block_count_cols,
            lane_xy,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        lane_base_13: &Lane<F>,
    ) -> Result<(Lane<F>, (Cell, Cell)), Error> {
        let cell = region.assign_advice(
            || format!("assign lane_{:?} === base_13_col", self.lane_xy),
            self.base_13_cols[0],
            offset,
            || Ok(lane_base_13_value),
        )?;
        region.constrain_equal(*lane_base_13, cell)?;

        let cell = region.assign_advice(
            || format!("assign lane_{:?} === base_9_col", self.lane_xy),
            self.base_9_cols[0],
            offset,
            || Ok(lane_base_9_value),
        )?;
        region.constrain_equal(*lane_base_9, cell)?;

        let mut offset = offset;

        for config in self.chunk_rotate_convert_configs.iter() {
            offset = config.assign_region(offset);
        }
        Ok(offset)
    }
}
