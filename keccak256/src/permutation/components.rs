use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, Error},
};
use itertools::Itertools;
use std::convert::TryInto;
use std::vec;

use super::tables::{LookupConfig, NUM_OF_BINARY_CHUNKS_PER_SLICE, NUM_OF_BINARY_SLICES};

use crate::{
    arith_helpers::{convert_b2_to_b13, convert_b2_to_b9, A1, A2, A3, A4, B13, B2, B9},
    common::{NEXT_INPUTS_LANES, PERMUTATION, ROTATION_CONSTANTS, ROUND_CONSTANTS},
    gate_helpers::{biguint_to_f, f_to_biguint},
    permutation::{
        generic::GenericConfig,
        rho_helpers::{slice_lane, RhoLane},
        tables::{NUM_OF_B9_CHUNKS_PER_SLICE, NUM_OF_B9_SLICES},
    },
};

use num_bigint::BigUint;

pub fn assign_theta<F: Field>(
    generic: &GenericConfig<F>,
    layouter: &mut impl Layouter<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let theta_col_sums = (0..5)
        .map(|x| {
            generic.running_sum(
                layouter,
                (0..5).map(|y| state[5 * x + y].clone()).collect(),
                None,
            )
        })
        .collect::<Result<Vec<_>, Error>>()?;

    let out_state = (0..5)
        .cartesian_product(0..5)
        .map(|(x, y)| {
            let cells = vec![
                state[5 * x + y].clone(),
                theta_col_sums[(x + 4) % 5].clone(),
                theta_col_sums[(x + 1) % 5].clone(),
            ];
            let vs = vec![F::one(), F::one(), F::from(B13 as u64)];
            generic.linear_combine_consts(layouter, cells, vs, None)
        })
        .collect::<Result<Vec<_>, Error>>()?;

    Ok(out_state.try_into().unwrap())
}

pub fn assign_rho<F: Field>(
    layouter: &mut impl Layouter<F>,
    lookup_config: &LookupConfig<F>,
    generic: &GenericConfig<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let mut next_state = vec![];
    let mut step2_od_join = vec![];
    let mut step3_od_join = vec![];
    for (lane_idx, lane) in state.iter().enumerate() {
        let rotation = {
            let x = lane_idx / 5;
            let y = lane_idx % 5;
            ROTATION_CONSTANTS[x][y]
        };
        let (conversions, special) =
            RhoLane::new(f_to_biguint(*lane.value().unwrap_or(&F::zero())), rotation)
                .get_full_witness();
        let slices = slice_lane(rotation);

        let (input_coefs, mut output_coefs, step2_od, step3_od) =
            lookup_config.assign_base13(layouter, &slices, &conversions)?;

        let input_pobs = conversions
            .iter()
            .map(|c| biguint_to_f::<F>(&c.input.power_of_base))
            .collect_vec();

        let mut output_pobs = conversions
            .iter()
            .map(|c| biguint_to_f::<F>(&c.output.power_of_base))
            .collect_vec();
        // Final output power of base
        output_pobs.push(biguint_to_f::<F>(&special.output_pob));

        let input_from_chunks =
            generic.linear_combine_consts(layouter, input_coefs, input_pobs, None)?;
        let last_chunk = generic.sub_advice(layouter, lane, &input_from_chunks)?;

        let final_output_coef = lookup_config.lookup_special_chunks(layouter, &last_chunk)?;
        output_coefs.push(final_output_coef);

        let output_lane =
            generic.linear_combine_consts(layouter, output_coefs, output_pobs, None)?;
        next_state.push(output_lane);
        step2_od_join.extend(step2_od);
        step3_od_join.extend(step3_od);
    }
    let step2_sum = generic.running_sum(layouter, step2_od_join, None)?;
    let step3_sum = generic.running_sum(layouter, step3_od_join, None)?;
    lookup_config.lookup_range_12(layouter, &[step2_sum])?;
    lookup_config.lookup_range_169(layouter, &[step3_sum])?;
    Ok(next_state.try_into().unwrap())
}

/// The Keccak Pi step
///
/// It has no gates. We just have to permute the previous state into the correct
/// order. The copy constrain in the next gate can then enforce the Pi step
/// permutation.
pub fn pi_gate_permutation<F: Field>(state: &[AssignedCell<F, F>; 25]) -> [AssignedCell<F, F>; 25] {
    (0..5)
        .cartesian_product(0..5)
        .map(|(x, y)| state[5 * ((x + 3 * y) % 5) + x].clone())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

pub fn assign_xi<F: Field>(
    generic: &GenericConfig<F>,
    layouter: &mut impl Layouter<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let out_state = (0..5)
        .cartesian_product(0..5)
        .map(|(x, y)| {
            let cells = vec![
                state[5 * x + y].clone(),
                state[5 * ((x + 1) % 5) + y].clone(),
                state[5 * ((x + 2) % 5) + y].clone(),
            ];
            let vs = vec![F::from(A1), F::from(A2), F::from(A3)];
            generic.linear_combine_consts(layouter, cells, vs, None)
        })
        .collect::<Result<Vec<_>, Error>>()?;
    Ok(out_state.try_into().unwrap())
}

#[derive(Clone, Debug)]
pub struct IotaConstants<F> {
    pub round_constant_b13: F,
    pub a4_times_round_constants_b9: [F; PERMUTATION],
}

impl<F: Field> Default for IotaConstants<F> {
    fn default() -> Self {
        let round_constant_b13 =
            biguint_to_f::<F>(&convert_b2_to_b13(ROUND_CONSTANTS[PERMUTATION - 1]));

        let a4_times_round_constants_b9: [F; 24] = ROUND_CONSTANTS
            .iter()
            .map(|&x| {
                let constant = A4 * convert_b2_to_b9(x);
                biguint_to_f::<F>(&constant)
            })
            .collect_vec()
            .try_into()
            .unwrap();

        Self {
            round_constant_b13,
            a4_times_round_constants_b9,
        }
    }
}

pub fn assign_next_input<F: Field>(
    layouter: &mut impl Layouter<F>,
    next_input_col: &Column<Advice>,
    next_input: &Option<[F; NEXT_INPUTS_LANES]>,
) -> Result<[AssignedCell<F, F>; NEXT_INPUTS_LANES], Error> {
    let next_input_b9 = layouter.assign_region(
        || "next input words",
        |mut region| {
            let next_input = next_input.map_or(
                [None; NEXT_INPUTS_LANES],
                |v| -> [Option<F>; NEXT_INPUTS_LANES] {
                    v.map(|vv| Some(vv))
                        .iter()
                        .cloned()
                        .collect_vec()
                        .try_into()
                        .unwrap()
                },
            );
            next_input
                .iter()
                .enumerate()
                .map(|(offset, input)| {
                    region.assign_advice(
                        || "next input words",
                        *next_input_col,
                        offset,
                        || Ok(input.unwrap_or_default()),
                    )
                })
                .collect::<Result<Vec<_>, Error>>()
        },
    )?;
    Ok(next_input_b9.try_into().unwrap())
}

pub fn convert_to_b9_mul_a4<F: Field>(
    layouter: &mut impl Layouter<F>,
    lookup_config: &LookupConfig<F>,
    generic: &GenericConfig<F>,
    next_input: &[AssignedCell<F, F>; NEXT_INPUTS_LANES],
) -> Result<[AssignedCell<F, F>; NEXT_INPUTS_LANES], Error> {
    let next_input = next_input
        .iter()
        .map(|input| {
            let (base2s, base9s, _) = lookup_config.assign_base2(layouter, input)?;
            let vs = (0..NUM_OF_BINARY_SLICES)
                .map(|i| {
                    biguint_to_f(
                        &BigUint::from(B2).pow((NUM_OF_BINARY_CHUNKS_PER_SLICE * i) as u32),
                    )
                })
                .rev()
                .collect_vec();
            generic.linear_combine_consts(layouter, base2s, vs, Some(input.clone()))?;
            let vs = (0..NUM_OF_BINARY_SLICES)
                .map(|i| {
                    biguint_to_f::<F>(
                        &BigUint::from(B9).pow((NUM_OF_BINARY_CHUNKS_PER_SLICE * i) as u32),
                    ) * F::from(A4)
                })
                .rev()
                .collect_vec();
            let output = generic.linear_combine_consts(layouter, base9s, vs, None)?;
            Ok(output)
        })
        .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;
    let next_input: [AssignedCell<F, F>; NEXT_INPUTS_LANES] = next_input.try_into().unwrap();
    Ok(next_input)
}

pub fn convert_from_b9_to_b13<F: Field>(
    layouter: &mut impl Layouter<F>,
    lookup_config: &LookupConfig<F>,
    generic: &GenericConfig<F>,
    state: [AssignedCell<F, F>; 25],
    output_b2: bool,
) -> Result<([AssignedCell<F, F>; 25], Option<[AssignedCell<F, F>; 25]>), Error> {
    let (state_b13, state_b2): (Vec<AssignedCell<F, F>>, Vec<Option<AssignedCell<F, F>>>) = state
        .iter()
        .map(|lane| {
            let (base9s, base_13s, base_2s) = lookup_config.assign_base9(layouter, lane)?;
            let vs = (0..NUM_OF_B9_SLICES)
                .map(|i| {
                    biguint_to_f(&BigUint::from(B9).pow((NUM_OF_B9_CHUNKS_PER_SLICE * i) as u32))
                })
                .rev()
                .collect_vec();
            generic.linear_combine_consts(layouter, base9s, vs, Some(lane.clone()))?;
            let vs = (0..NUM_OF_B9_SLICES)
                .map(|i| {
                    biguint_to_f(&BigUint::from(B13).pow((NUM_OF_B9_CHUNKS_PER_SLICE * i) as u32))
                })
                .rev()
                .collect_vec();
            let lane_b13 = generic.linear_combine_consts(layouter, base_13s, vs, None)?;
            let lane_b2 = if output_b2 {
                let vs = (0..NUM_OF_B9_SLICES)
                    .map(|i| {
                        biguint_to_f(
                            &BigUint::from(B2).pow((NUM_OF_B9_CHUNKS_PER_SLICE * i) as u32),
                        )
                    })
                    .rev()
                    .collect_vec();
                let lane_b2 = generic.linear_combine_consts(layouter, base_2s, vs, None)?;
                Some(lane_b2)
            } else {
                None
            };
            Ok((lane_b13, lane_b2))
        })
        .collect::<Result<Vec<_>, Error>>()?
        .iter()
        .cloned()
        .unzip();
    let state_b2: Option<[AssignedCell<F, F>; 25]> = state_b2
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .map(|v| v.try_into().unwrap());

    Ok((state_b13.try_into().unwrap(), state_b2))
}
