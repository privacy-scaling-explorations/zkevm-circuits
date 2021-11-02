use crate::arith_helpers::*;
use crate::common::{LANE_SIZE, ROTATION_CONSTANTS};
use crate::gates::gate_helpers::*;
use crate::gates::tables::*;
use halo2::{
    circuit::{Layouter, Region},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector,
    },
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use pasta_curves::arithmetic::FieldExt;
use std::iter;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct RotatingVariables {
    rotation: u32,
    chunk_idx: u32,
    step: u32,
    input_raw: BigUint,
    input_coef: BigUint,
    input_power_of_base: BigUint,
    input_acc: BigUint,
    output_coef: BigUint,
    output_power_of_base: BigUint,
    output_acc: BigUint,
    block_count: u32,
    // step2 acc and step3 acc
    block_count_acc: [u32; 2],
    low_value: BigUint,
    high_value: Option<BigUint>,
}

impl RotatingVariables {
    fn from(lane_base_13: BigUint, rotation: u32) -> Result<Self, Error> {
        let chunk_idx = 1;
        let step = get_step_size(chunk_idx, rotation);
        let input_raw = lane_base_13.clone() / B13;
        let input_coef = input_raw.clone() % B13.pow(step);
        let input_power_of_base = BigUint::from(B13);
        let input_acc = lane_base_13.clone();
        let (block_count, output_coef) =
            get_block_count_and_output_coef(input_coef.clone());
        let output_coef = BigUint::from(output_coef);
        let output_power_of_base = if is_at_rotation_offset(chunk_idx, rotation)
        {
            BigUint::one()
        } else {
            BigUint::from(B9).pow(rotation + chunk_idx)
        };
        let output_acc = BigUint::zero();
        let mut block_count_acc = [0; 2];
        if step == 2 || step == 3 {
            block_count_acc[(step - 2) as usize] += block_count;
        }
        let low_value = lane_base_13 % B13;
        Ok(Self {
            rotation,
            chunk_idx,
            step,
            input_raw,
            input_coef,
            input_power_of_base,
            input_acc,
            output_coef,
            output_power_of_base,
            output_acc,
            block_count,
            block_count_acc,
            low_value,
            high_value: None,
        })
    }

    fn next(&self) -> Self {
        assert!(self.chunk_idx < LANE_SIZE);
        let mut new = self.clone();
        new.chunk_idx += self.step;
        new.step = get_step_size(new.chunk_idx, self.rotation);
        new.input_raw /= B13.pow(self.step);
        new.input_coef = new.input_raw.clone() % B13.pow(new.step);
        new.input_power_of_base *= B13.pow(self.step);
        new.input_acc -=
            self.input_power_of_base.clone() * self.input_coef.clone();
        let (block_count, output_coef) =
            get_block_count_and_output_coef(new.input_coef.clone());
        new.output_coef = BigUint::from(output_coef);
        new.output_power_of_base =
            if is_at_rotation_offset(new.chunk_idx, self.rotation) {
                BigUint::one()
            } else {
                self.output_power_of_base.clone() * B9.pow(self.step)
            };
        new.output_acc +=
            self.output_power_of_base.clone() * self.output_coef.clone();
        new.block_count = block_count;
        if self.step == 2 || self.step == 3 {
            new.block_count_acc[(self.step - 2) as usize] += block_count;
        }
        if new.chunk_idx >= LANE_SIZE {
            new.high_value = Some(self.input_raw.clone() % B13);
        }
        new
    }
}

#[derive(Debug, Clone)]
// TODO: make STEP and BASE const generics, make `slice` a fixed column.
pub struct RunningSumConfig<F> {
    q_enable: Selector,
    coef: Column<Advice>,
    power_of_base: Column<Advice>,
    accumulator: Column<Advice>,
    step: u32,
    base: u64,
    is_input: bool,
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
    ) -> Self {
        let config = Self {
            q_enable,
            coef: cols[0],
            power_of_base: cols[1],
            accumulator: cols[2],
            step,
            base,
            is_input,
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
                // .chain(Some((
                //     // TODO: this check should failed at the output power of base due to the rotation
                //     "next_power_of_base === power_of_base * base_to_step",
                //     next_power_of_base - power_of_base * base_to_step,
                // )))
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

#[derive(Debug, Clone)]
pub struct SpecialChunkConfig<F> {
    q_enable: Selector,
    last_b9_coef: Column<Advice>,
    rotation: u64,
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
        last_b9_coef: Column<Advice>,
        special: [Column<Fixed>; 2],
        rotation: u64,
    ) -> Self {
        meta.create_gate("validate base_9_acc", |meta| {
            let delta_base_9_acc = meta
                .query_advice(base_9_acc, Rotation::next())
                - meta.query_advice(base_9_acc, Rotation::cur());
            let last_b9_coef = meta.query_advice(last_b9_coef, Rotation::cur());
            let pow_of_9 =
                Expression::Constant(F::from_u64(B9).pow(&[rotation, 0, 0, 0]));
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
            special,
        );
        Self {
            q_enable,
            last_b9_coef,
            rotation,
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
        high_value: &BigUint,
        base_13_acc: &BigUint,
        base_9_acc: &BigUint,
    ) -> Result<Lane<F>, Error> {
        self.q_enable.enable(region, offset)?;
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
        let last_pow_of_9 = F::from_u64(B9).pow(&[self.rotation, 0, 0, 0]);
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

#[derive(Debug, Clone)]
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
                1 | 4 => vec![
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
        block_count: u32,
        block_count_acc: [u32; 2],
    ) -> Result<BlockCount2<F>, Error> {
        let block_count = F::from_u64(block_count.into());
        let block_count_acc = block_count_acc.map(|x| F::from_u64(x.into()));
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
            || Ok(block_count_acc[0]),
        )?;
        let block_count_step2 = BlockCount {
            cell: cell_step2,
            value: block_count_acc[0],
        };
        let cell_step3 = region.assign_advice(
            || "block_count",
            self.block_count_cols[2],
            offset,
            || Ok(block_count_acc[1]),
        )?;
        let block_count_step3 = BlockCount {
            cell: cell_step3,
            value: block_count_acc[1],
        };
        Ok((block_count_step2, block_count_step3))
    }
}

#[derive(Clone)]
pub struct BlockCountFinalConfig<F> {
    q_enable: Selector,
    block_count_cols: [Column<Advice>; 2],
    _marker: PhantomData<F>,
}
impl<F: FieldExt> BlockCountFinalConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        block_count_cols: [Column<Advice>; 2],
    ) -> Self {
        let q_enable = meta.selector();
        for column in block_count_cols.iter() {
            meta.enable_equality((*column).into());
        }

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
        block_count_cells: [BlockCount2<F>; 25],
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

#[derive(Debug, Clone)]
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
}

impl<F: FieldExt> ChunkRotateConversionConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        base_13_cols: [Column<Advice>; 3],
        base_9_cols: [Column<Advice>; 3],
        block_count_cols: [Column<Advice>; 3],
        fix_cols: [Column<Fixed>; 3],
        step: u32,
    ) -> Self {
        let base_13_to_base_9_lookup = Base13toBase9TableConfig::configure(
            meta,
            q_enable,
            base_13_cols[1],
            base_9_cols[1],
            block_count_cols[0],
            fix_cols,
        );

        let b13_rs_config = RunningSumConfig::configure(
            meta,
            q_enable,
            base_13_cols,
            step,
            B13,
            true,
        );

        let b9_rs_config = RunningSumConfig::configure(
            meta,
            q_enable,
            base_9_cols,
            step,
            B9,
            false,
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
        }
    }

    fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        rv: &mut RotatingVariables,
    ) -> Result<BlockCount2<F>, Error> {
        self.b13_rs_config.assign_region(
            region,
            offset,
            &rv.input_coef,
            &rv.input_power_of_base,
            &rv.input_acc,
        )?;
        self.b9_rs_config.assign_region(
            region,
            offset,
            &rv.output_coef,
            &rv.output_power_of_base,
            &rv.output_acc,
        )?;
        let block_counts = self.block_count_acc_config.assign_region(
            region,
            offset,
            rv.block_count,
            rv.block_count_acc,
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
    // near the rotation offset position of the lane
    let offset = LANE_SIZE - rotation;
    if chunk_idx < offset && offset < chunk_idx + BASE_NUM_OF_CHUNKS {
        return offset - chunk_idx;
    }
    // near the end of the lane
    if chunk_idx < LANE_SIZE && LANE_SIZE < chunk_idx + BASE_NUM_OF_CHUNKS {
        return LANE_SIZE - chunk_idx;
    }
    BASE_NUM_OF_CHUNKS
}
/// This is the point where power of 9 starts from 1
fn is_at_rotation_offset(chunk_idx: u32, rotation: u32) -> bool {
    chunk_idx == LANE_SIZE - rotation
}

fn slice_lane(rotation: u32) -> Vec<(u32, u32)> {
    // we start chunk_idx from 1
    // because the 0th chunk is for the low value from the theta step
    let mut chunk_idx = 1;
    let mut output = vec![];
    while chunk_idx < LANE_SIZE {
        let step = get_step_size(chunk_idx, rotation);
        output.push((chunk_idx, step));
        chunk_idx += step;
    }
    output
}

fn block_counting_function(n: usize) -> u32 {
    [0, 0, 1, 13, 170][n]
}

fn get_block_count_and_output_coef(input_coef: BigUint) -> (u32, u64) {
    let mut x = input_coef;
    let mut output_coef = 0;
    let mut non_zero_chunk_count = 0;
    for i in 0..4 {
        let base13_chunk = match (x.clone() % B13).to_u64_digits().first() {
            Some(d) => *d,
            None => 0u64,
        };
        let base9_chunk = convert_b13_coef(base13_chunk);
        if base9_chunk != 0 {
            non_zero_chunk_count += 1;
        }
        output_coef += base9_chunk * B9.pow(i as u32);
        x /= B13;
    }
    let block_count = block_counting_function(non_zero_chunk_count);

    (block_count, output_coef)
}

#[derive(Debug, Clone)]
pub struct LaneRotateConversionConfig<F> {
    q_enable: Selector,
    q_is_special: Selector,
    // coef, power_of_13, acc
    base_13_cols: [Column<Advice>; 3],
    // coef, power_of_9, acc
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
        rotate_conversion: [[Column<Advice>; 3]; 3],
        axiliary: [Column<Advice>; 2],
        base13_to_9: [Column<Fixed>; 3],
        special: [Column<Fixed>; 2],
    ) -> Self {
        let [base_13_cols, base_9_cols, block_count_cols] = rotate_conversion;
        meta.enable_equality(base_13_cols[2].into());
        meta.enable_equality(base_9_cols[2].into());
        let q_enable = meta.selector();
        let q_is_special = meta.selector();
        let rotation = ROTATION_CONSTANTS[lane_xy.0][lane_xy.1];
        let slices = slice_lane(rotation);
        let chunk_rotate_convert_configs = slices
            .iter()
            .map(|(_, step)| {
                ChunkRotateConversionConfig::configure(
                    q_enable,
                    meta,
                    base_13_cols,
                    base_9_cols,
                    block_count_cols,
                    base13_to_9,
                    *step,
                )
            })
            .collect::<Vec<_>>();
        let special_chunk_config = SpecialChunkConfig::configure(
            meta,
            q_is_special,
            base_13_cols[2],
            base_9_cols[2],
            axiliary[0],
            special,
            rotation as u64,
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
    ) -> Result<(Lane<F>, BlockCount2<F>), Error> {
        let (lane, block_counts) = layouter.assign_region(
            || format!("LRCC {:?}", self.lane_xy),
            |mut region| {
                let mut offset = 0;
                let cell = region.assign_advice(
                    || "base_13_col",
                    self.base_13_cols[2],
                    offset,
                    || Ok(lane_base_13.value),
                )?;
                region.constrain_equal(lane_base_13.cell, cell)?;

                offset += 1;

                let mut rv = RotatingVariables::from(
                    f_to_biguint(lane_base_13.value)
                        .ok_or(Error::SynthesisError)?,
                    self.rotation,
                )?;
                let all_block_counts: Result<Vec<BlockCount2<F>>, Error> = self
                    .chunk_rotate_convert_configs
                    .iter()
                    .map(|config| {
                        let block_counts = config.assign_region(
                            &mut region,
                            offset,
                            &mut rv,
                        )?;
                        offset += 1;
                        rv = rv.next();
                        Ok(block_counts)
                    })
                    .collect();
                let all_block_counts = all_block_counts?;
                let block_counts =
                    all_block_counts.last().ok_or(Error::SynthesisError)?;
                let lane = self.special_chunk_config.assign_region(
                    &mut region,
                    offset,
                    &rv.low_value,
                    &rv.high_value.ok_or(Error::SynthesisError)?,
                    &rv.input_acc,
                    &rv.output_acc,
                )?;
                Ok((lane, *block_counts))
            },
        )?;
        Ok((lane, block_counts))
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.chunk_rotate_convert_configs[0]
            .base_13_to_base_9_lookup
            .load(layouter)?;
        self.special_chunk_config
            .special_chunk_table_config
            .load(layouter)?;
        Ok(())
    }
}
