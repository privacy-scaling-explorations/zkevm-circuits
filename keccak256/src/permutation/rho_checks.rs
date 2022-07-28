//! Inner checks in the Rho step
//!
//! ## Overview
//!
//! In the Rho checks we convert each lane from base 13 to base 9.
//! We call the base 13 lane the input and the base 9 lane the output.
//! We can view the lane as a polynomial
//! - where the input lane is `A(13) =  a0 13^0 + ... + a64 13^64`, and
//! - the output lane is  `B(9)  =  b0  9^0 + ... + b63  9^63`
//!
//! We call the a coefficient of the polynomial a chunk.
//!
//! The output chunks represent the output bits of the lane in binary, in little
//! endian.
//!
//! Note that the input lane is special because it's an output from the Theta
//! step, so it has 65 chunks. It holds that `0 <= a0 + a64 < 13`. We refer a0
//! to be low value and a64 high value.
//!
//! In the Rho step we perform the **rotation** of chunk positions and the
//! **conversion** from base 13 to base 9.
//!
//! More formally speaking, we have a transform `T`, where `bi = T(aj)` for some
//! `i`, `j`, and `ai` is not special chunks.
//! For special chunk, `bi = T(a0 + a64)`.
//!
//! - The rotate means we perform the rotate left of the rotation specified in
//!   `ROTATION_CONSTANTS`. Say if our rotation is 3,
//! The a1 will be contribute to b3, and a63 will go to b0.
//!
//! The convert `T` is the [`crate::arith_helpers::convert_b13_coef`], in the
//! circuit we have to do a lookup check for that
//!
//! The lookup is more efficient when we lookup
//! multiple([`crate::permutation::rho_helpers::BASE_NUM_OF_CHUNKS`]) chunks at
//! a time.
//!
//! ## Checks
//!
//! The goal is to check the conversion from the base 13 input lane to the base
//! 9 output lane is sound.
//!
//! ### The Normal Slices
//!
//! For each lane, we split up the lane in slices of chunks.
//! - We run down the input accumulator by subtracting each `input_coef *
//!   power_of_13`
//! - We run up the output accumulator by adding up `output_coef * power_of_9`
//! - We lookup [`crate::permutation::tables::Base13toBase9TableConfig`] and
//!   check the conversion between `input_coef` and `output_coef` is valid
//!
//! We have the copy constraint to glue input accumulator to input lane and the
//! output accumulator to output lane
//!
//! But we have special checks to do
//!
//! ### Sepcial Chunks
//!
//! The Theta step shifted left 1 chunk. So the base 13 input lane now has 65
//! chunks, where the 0th and the 64th input chunks contribute to the same
//! output chunk. We call the 0th input chunk the `low_value` and the 64th input
//! chunk the `high_value`. A the end of the running down input accumulator, the
//! remaining value is `low_value + high_value * 13**64` We lookup [`crate::
//! permutation::tables::SpecialChunkTableConfig`] to convert it to
//! `convert_b13_coef(low_value + high_value)`.
//!
//! ### Overflow Checks
//!
//! The [`crate::permutation::tables::Base13toBase9TableConfig`] table is built
//! to lookup 4 chunks. But we have chunks that are step 1, step 2, and step 3,
//! which means they suppose to have the last 1, 2, or 3 chunks to be 0.
//! If a step 1 step is witnessed with 2, 3, or 4 non-zero input chunks, then
//! it's a malicious overflow and we have to provent the prover from doing that.
//!
//! Doing range check for each of non-4chunks steps would be inefficient,
//! instead we use the following technique.
//!
//! We define the [`crate::permutation::rho_helpers::OVERFLOW_TRANSFORM`] to map
//! `step` to a value `overflow_detector`. We also add a column in
//! [`crate::permutation::tables::Base13toBase9TableConfig`] to lookup
//! `overflow_detector`. We sum up all the overflow_detectors across 25 lanes,
//! for each step 1, step 2, and step 3. At the end of the Rho step we perform
//! the final overflow detector range check for them.
//!
//! The `OVERFLOW_TRANSFORM` maps step 1 to 0, step 2 to 1, step 3 to 13, and
//! step 4 to 170. It is defined that any possible overflow would result the
//! final overflow detector check to fail.
//!
//! It would be better explained if we enumerate all the possible cases:
//!
//! The sum of the step 1 should be 0.
//! So that if prover witness any more than 1 non-zero chunks, the
//! [`crate::permutation::tables::Base13toBase9TableConfig`] returns a overflow
//! detector 1, 13, or 170 and fail the final sum check.
//!
//! The sum of the step 2 should be less than or equal to 1 times all numbers of
//! step 2, which can be counted at setup time to be 12. So that if prover
//! witness any more than 2 non-zero chunks, the
//! [`crate::permutation::tables::Base13toBase9TableConfig`] returns a overflow
//! detector 13 or 170 and fail the final sum check.
//!
//! The sum of the step 3 should be less than or equal to 13 times all numbers
//! of step 3, which can be counted at setup time to be 13. So that if prover
//! witness any more than 3 non-zero chunks, the
//! [`crate::permutation::tables::Base13toBase9TableConfig`] returns a overflow
//! detector 170 and fail the final sum check.
use crate::arith_helpers::*;
use crate::common::ROTATION_CONSTANTS;
use crate::gate_helpers::{biguint_to_f, f_to_biguint};
use crate::permutation::{
    generic::GenericConfig,
    rho_helpers::*,
    tables::{Base13toBase9TableConfig, StackableTable},
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct LaneRotateConversionConfig<F> {
    q_normal: Selector,
    input_coef: Column<Advice>,
    output_coef: Column<Advice>,
    overflow_detector: Column<Advice>,
    generic: GenericConfig<F>,
    stackable: StackableTable<F>,
}

impl<F: Field> LaneRotateConversionConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        base13_to_9_table: &Base13toBase9TableConfig<F>,
        advices: [Column<Advice>; 3],
        constant: Column<Fixed>,
        generic: GenericConfig<F>,
        stackable: StackableTable<F>,
    ) -> Self {
        let q_normal = meta.complex_selector();
        let [input_coef, output_coef, overflow_detector] = advices;

        meta.enable_equality(overflow_detector);
        meta.enable_constant(constant);

        meta.lookup("b13 -> b9 table", |meta| {
            let q_normal = meta.query_selector(q_normal);
            let base13_coef = meta.query_advice(input_coef, Rotation::cur());
            let base9_coef = meta.query_advice(output_coef, Rotation::cur());
            let od = meta.query_advice(overflow_detector, Rotation::cur());

            vec![
                (q_normal.clone() * base13_coef, base13_to_9_table.base13),
                (q_normal.clone() * base9_coef, base13_to_9_table.base9),
                (q_normal * od, base13_to_9_table.overflow_detector),
            ]
        });
        Self {
            q_normal,
            input_coef,
            output_coef,
            overflow_detector,
            generic,
            stackable,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        lane_base_13: AssignedCell<F, F>,
        lane_idx: usize,
    ) -> Result<
        (
            AssignedCell<F, F>,
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
        ),
        Error,
    > {
        let rotation = {
            let x = lane_idx / 5;
            let y = lane_idx % 5;
            ROTATION_CONSTANTS[x][y]
        };
        let (conversions, special) = RhoLane::new(
            f_to_biguint(*lane_base_13.value().unwrap_or(&F::zero())),
            rotation,
        )
        .get_full_witness();
        let slices = slice_lane(rotation);

        let (input_coefs, input_pobs, output_coefs, output_pobs, step2_od, step3_od) = layouter
            .assign_region(
                || "lane rotate conversion",
                |mut region| {
                    let mut input_coefs: Vec<AssignedCell<F, F>> = vec![];
                    let mut output_coefs: Vec<AssignedCell<F, F>> = vec![];
                    let mut input_pobs: Vec<F> = vec![];
                    let mut output_pobs: Vec<F> = vec![];
                    let mut step2_od: Vec<AssignedCell<F, F>> = vec![];
                    let mut step3_od: Vec<AssignedCell<F, F>> = vec![];
                    for (offset, (&(chunk_idx, step), conv)) in
                        slices.iter().zip(conversions.iter()).enumerate()
                    {
                        self.q_normal.enable(&mut region, offset)?;
                        let input_coef = region.assign_advice(
                            || format!("Input Coef {}", chunk_idx),
                            self.input_coef,
                            offset,
                            || Ok(biguint_to_f::<F>(&conv.input.coef)),
                        )?;
                        input_coefs.push(input_coef);
                        input_pobs.push(biguint_to_f::<F>(&conv.input.power_of_base));
                        let output_coef = region.assign_advice(
                            || "Output Coef",
                            self.output_coef,
                            offset,
                            || Ok(biguint_to_f::<F>(&conv.output.coef)),
                        )?;
                        output_coefs.push(output_coef);
                        output_pobs.push(biguint_to_f::<F>(&conv.output.power_of_base));

                        let od = region.assign_advice(
                            || "Overflow detector",
                            self.overflow_detector,
                            offset,
                            || Ok(F::from(conv.overflow_detector.value as u64)),
                        )?;
                        match step {
                            1 => region.constrain_constant(od.cell(), F::zero())?,
                            2 => step2_od.push(od),
                            3 => step3_od.push(od),
                            4 => { // Do nothing
                            }
                            _ => unreachable!(),
                        }
                    }
                    // Special chunk
                    let final_output_coef = region.assign_advice(
                        || "Special output coef",
                        self.output_coef,
                        slices.len(),
                        || Ok(F::from(special.output_coef as u64)),
                    )?;
                    let final_output_pob = F::from(B9 as u64).pow(&[rotation.into(), 0, 0, 0]);
                    output_coefs.push(final_output_coef);
                    output_pobs.push(final_output_pob);

                    Ok((
                        input_coefs,
                        input_pobs,
                        output_coefs,
                        output_pobs,
                        step2_od,
                        step3_od,
                    ))
                },
            )?;
        let input_from_chunks =
            self.generic
                .linear_combine_consts(layouter, input_coefs, input_pobs, None)?;
        let diff = self
            .generic
            .sub_advice(layouter, lane_base_13, input_from_chunks)?;

        self.stackable
            .lookup_special_chunks(layouter, &diff, output_coefs.last().unwrap())?;

        let output_lane =
            self.generic
                .linear_combine_consts(layouter, output_coefs, output_pobs, None)?;
        Ok((output_lane, step2_od, step3_od))
    }
}
