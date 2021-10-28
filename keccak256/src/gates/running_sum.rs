use crate::arith_helpers::*;
use crate::common::ROTATION_CONSTANTS;
use crate::gates::gate_helpers::*;
use crate::gates::tables::*;
use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use pasta_curves::arithmetic::FieldExt;
use std::iter;
use std::marker::PhantomData;

#[derive(Debug)]
// TODO: make STEP and BASE const generics, make `slice` a fixed column.
pub struct RunningSumConfig<F> {
    q_enable: Selector,
    coef: Column<Advice>,
    power_of_base: Column<Advice>,
    accumulator: Column<Advice>,
    step: u32,
    base: u64,
    is_input: bool,
    rotation: u32,
    chunk_idx: u32,
    _marker: PhantomData<F>,
}
impl<F: FieldExt> RunningSumConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        cols: [Column<Advice>; 3],
        step: u32,
        base: u64,
        is_input: bool,
        rotation: u32,
        chunk_idx: u32,
    ) -> Self {
        let config = Self {
            q_enable,
            coef: cols[0],
            power_of_base: cols[1],
            accumulator: cols[2],
            step,
            base,
            is_input,
            rotation,
            chunk_idx,
            _marker: PhantomData,
        };
        meta.create_gate("mul", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let coef = meta.query_advice(config.coef, Rotation::cur());
            let power_of_base =
                meta.query_advice(config.power_of_base, Rotation::cur());
            let delta_acc = meta
                .query_advice(config.accumulator, Rotation::next())
                - meta.query_advice(config.accumulator, Rotation::cur());
            let next_power_of_base =
                meta.query_advice(config.power_of_base, Rotation::next());
            let base_to_step =
                Expression::Constant(F::from(u64::pow(base, step)));
            let running_poly = match is_input {
                true => (
                    "delta_acc === - coef * power_of_base", // running down for input
                    delta_acc + coef * power_of_base.clone(),
                ),
                false => (
                    "delta_acc === coef * power_of_base", // running up for output
                    delta_acc - coef * power_of_base.clone(),
                ),
            };
            iter::empty()
                .chain(Some(running_poly))
                .chain(Some((
                    "next_power_of_base === power_of_base * base_to_step",
                    next_power_of_base - power_of_base * base_to_step,
                )))
                .map(|(name, poly)| (name, q_enable.clone() * poly))
                .collect::<Vec<_>>()
        });
        config
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        coef: &BigUint,
        power_of_base: &BigUint,
        acc: &BigUint,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "coef",
            self.coef,
            offset,
            || biguint_to_f::<F>(coef.clone()).ok_or(Error::SynthesisError),
        )?;
        region.assign_advice(
            || "power_of_base",
            self.power_of_base,
            offset,
            || {
                biguint_to_f::<F>(power_of_base.clone())
                    .ok_or(Error::SynthesisError)
            },
        )?;
        region.assign_advice(
            || "accumulator",
            self.accumulator,
            offset,
            || biguint_to_f::<F>(acc.clone()).ok_or(Error::SynthesisError),
        )?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct SpecialChunkConfig<F> {
    q_enable: Selector,
    last_b9_coef: Column<Advice>,
    keccak_rotation: u32,
    base_13_acc: Column<Advice>,
    base_9_acc: Column<Advice>,
    special_chunk_table_config: SpecialChunkTableConfig<F>,
}

impl<F: FieldExt> SpecialChunkConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        base_13_acc: Column<Advice>,
        base_9_acc: Column<Advice>,
        keccak_rotation: u32,
    ) -> Self {
        let last_b9_coef = meta.advice_column();
        meta.create_gate("validate base_9_acc", |meta| {
            let delta_base_9_acc = meta
                .query_advice(base_9_acc, Rotation::next())
                - meta.query_advice(base_9_acc, Rotation::cur());
            let last_b9_coef = meta.query_advice(last_b9_coef, Rotation::cur());
            let pow_of_9 = Expression::Constant(
                F::from_u64(B9.pow(keccak_rotation)).pow(&[
                    keccak_rotation as u64,
                    0,
                    0,
                    0,
                ]),
            );
            vec![(
                "delta_base_9_acc === (high_value + low_value) * 9**rotation",
                meta.query_selector(q_enable)
                    * (delta_base_9_acc - last_b9_coef * pow_of_9),
            )]
        });
        let special_chunk_table_config = SpecialChunkTableConfig::configure(
            meta,
            q_enable,
            base_13_acc,
            last_b9_coef,
        );
        Self {
            q_enable,
            last_b9_coef,
            keccak_rotation,
            base_13_acc,
            base_9_acc,
            special_chunk_table_config,
        }
    }
    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        low_value: &BigUint,
        base_13_acc: &BigUint,
        base_9_acc: &BigUint,
    ) -> Result<Lane<F>, Error> {
        self.q_enable.enable(region, offset)?;
        let high_value = base_13_acc % B13;
        region.assign_advice(
            || "input_acc",
            self.base_13_acc,
            offset,
            || {
                biguint_to_f::<F>(base_13_acc.clone())
                    .ok_or(Error::SynthesisError)
            },
        )?;
        region.assign_advice(
            || "input_acc_last",
            self.base_13_acc,
            offset + 1,
            || Ok(F::zero()),
        )?;
        let base_9_acc = biguint_to_f::<F>(base_9_acc.clone())
            .ok_or(Error::SynthesisError)?;
        region.assign_advice(
            || "ouput_acc",
            self.base_9_acc,
            offset,
            || Ok(base_9_acc),
        )?;
        let last_pow_of_9 =
            F::from_u64(B9).pow(&[self.keccak_rotation as u64, 0, 0, 0]);
        let last_b9_coef = biguint_to_f::<F>((high_value + low_value) % 2u64)
            .ok_or(Error::SynthesisError)?;
        let value = base_9_acc + last_b9_coef * last_pow_of_9;
        let cell = region.assign_advice(
            || "ouput_acc_last",
            self.base_9_acc,
            offset + 1,
            || Ok(value),
        )?;
        Ok(Lane { cell, value })
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

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block_count: F,
        step2_acc: F,
        step3_acc: F,
    ) -> Result<(BlockCount<F>, BlockCount<F>), Error> {
        region.assign_advice(
            || "block_count",
            self.block_count_cols[0],
            offset,
            || Ok(block_count),
        )?;
        let cell_step2 = region.assign_advice(
            || "block_count",
            self.block_count_cols[1],
            offset,
            || Ok(step2_acc),
        )?;
        let block_count_step2 = BlockCount {
            cell: cell_step2,
            value: step2_acc,
        };
        let cell_step3 = region.assign_advice(
            || "block_count",
            self.block_count_cols[2],
            offset,
            || Ok(step3_acc),
        )?;
        let block_count_step3 = BlockCount {
            cell: cell_step3,
            value: step3_acc,
        };
        Ok((block_count_step2, block_count_step3))
    }
}

pub struct BlockCountFinalConfig<F> {
    q_enable: Selector,
    block_count_cols: [Column<Advice>; 2],
    _marker: PhantomData<F>,
}
impl<F: FieldExt> BlockCountFinalConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let block_count_cols = [meta.advice_column(); 2];

        meta.create_gate("block count final check", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let step2_acc =
                meta.query_advice(block_count_cols[0], Rotation::cur());
            let step3_acc =
                meta.query_advice(block_count_cols[1], Rotation::cur());
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
        block_count_cells: [(BlockCount<F>, BlockCount<F>); 25],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "final block count",
            |mut region| {
                for (offset, bc) in block_count_cells.iter().enumerate() {
                    self.q_enable.enable(&mut region, offset)?;
                    let cell_1 = region.assign_advice(
                        || format!("block_count step2 acc lane {}", offset),
                        self.block_count_cols[0],
                        offset,
                        || Ok(bc.0.value),
                    )?;
                    region.constrain_equal(cell_1, bc.0.cell)?;
                    let cell_2 = region.assign_advice(
                        || format!("block_count step3 acc lane {}", offset),
                        self.block_count_cols[1],
                        offset,
                        || Ok(bc.1.value),
                    )?;
                    region.constrain_equal(cell_2, bc.1.cell)?;
                }
                Ok(())
            },
        )?;
        Ok(())
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
    step: u32,
    rotation: u32,
    chunk_idx: u32,
}

impl<F: FieldExt> ChunkRotateConversionConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        base_13_cols: [Column<Advice>; 3],
        base_9_cols: [Column<Advice>; 3],
        block_count_cols: [Column<Advice>; 3],
        step: u32,
        rotation: u32,
        chunk_idx: u32,
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
            true,
            rotation,
            chunk_idx,
        );

        let b9_rs_config = RunningSumConfig::configure(
            meta,
            q_enable,
            base_9_cols,
            step,
            B9,
            false,
            rotation,
            chunk_idx,
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
            step,
            rotation,
            chunk_idx,
        }
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        input_raw: &mut BigUint,
        input_power_of_base: &mut BigUint,
        input_acc: &mut BigUint,
        output_power_of_base: &mut BigUint,
        output_acc: &mut BigUint,
        step2_acc: &mut F,
        step3_acc: &mut F,
    ) -> Result<(BlockCount<F>, BlockCount<F>), Error> {
        let input_base_to_step = B13.pow(self.step);
        let input_coef = input_raw.clone() % input_base_to_step;
        self.b13_rs_config.assign_region(
            region,
            offset,
            &input_coef,
            input_power_of_base,
            input_acc,
        )?;
        *input_acc -= input_power_of_base.clone() * input_coef;
        *input_raw /= input_base_to_step;
        *input_power_of_base *= input_base_to_step;

        let (block_count, output_coef) = self
            .base_13_to_base_9_lookup
            .get_block_count_and_output_coef();

        let output_base_to_step = B9.pow(self.step);
        let output_coef = BigUint::from(output_coef);
        self.b9_rs_config.assign_region(
            region,
            offset,
            &output_coef,
            output_power_of_base,
            output_acc,
        )?;
        *output_acc += output_power_of_base.clone() * output_coef;
        *output_power_of_base = if self.chunk_idx == 64 - self.rotation {
            BigUint::one()
        } else {
            output_power_of_base.clone() * output_base_to_step
        };

        let block_count = F::from(block_count as u64);

        if self.step == 2 {
            *step2_acc += block_count;
        };

        if self.step == 3 {
            *step3_acc += block_count;
        };
        let block_counts = self.block_count_acc_config.assign_region(
            region,
            offset,
            block_count,
            *step2_acc,
            *step3_acc,
        )?;
        Ok(block_counts)
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
    rotation: u32,
}

impl<F: FieldExt> LaneRotateConversionConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        lane_xy: (usize, usize),
    ) -> Self {
        let base_13_cols = [meta.advice_column(); 3];
        let base_9_cols = [meta.advice_column(); 3];
        let block_count_cols = [meta.advice_column(); 3];
        let q_enable = meta.selector();
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
                rotation,
                chunk_idx,
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
            rotation,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        lane_base_13: &Lane<F>,
    ) -> Result<(Lane<F>, (BlockCount<F>, BlockCount<F>)), Error> {
        let (lane, block_counts) = layouter.assign_region(
            || format!("lane {:?}", self.lane_xy),
            |mut region| {
                let mut offset = 0;
                let cell = region.assign_advice(
                    || "base_13_col",
                    self.base_13_cols[0],
                    offset,
                    || Ok(lane_base_13.value),
                )?;
                region.constrain_equal(lane_base_13.cell, cell)?;

                offset += 1;
                let mut all_block_counts = vec![];

                let mut input_raw = f_to_biguint(lane_base_13.value)
                    .ok_or(Error::SynthesisError)?;
                let mut input_power_of_base = BigUint::from(B13);
                let mut input_acc = input_raw.clone();
                let mut output_power_of_base = if self.rotation == 63 {
                    BigUint::one()
                } else {
                    BigUint::from(B9).pow(self.rotation + 1)
                };
                let mut output_acc = BigUint::zero();
                let mut step2_acc = F::zero();
                let mut step3_acc = F::zero();
                let low_value = input_raw.clone() % B13;

                for config in self.chunk_rotate_convert_configs.iter() {
                    let block_counts = config.assign_region(
                        &mut region,
                        offset,
                        &mut input_raw,
                        &mut input_power_of_base,
                        &mut input_acc,
                        &mut output_power_of_base,
                        &mut output_acc,
                        &mut step2_acc,
                        &mut step3_acc,
                    )?;
                    offset += 1;
                    all_block_counts.push(block_counts);
                }
                let lane = self.special_chunk_config.assign_region(
                    &mut region,
                    offset,
                    &low_value,
                    &input_acc,
                    &output_acc,
                )?;
                let block_counts =
                    all_block_counts.last().ok_or(Error::SynthesisError)?;
                Ok((lane, *block_counts))
            },
        )?;
        Ok((lane, block_counts))
    }
}
