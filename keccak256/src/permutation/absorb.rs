use crate::arith_helpers::*;
use crate::common::*;
use crate::gate_helpers::*;
use crate::permutation::add::AddConfig;
use eth_types::Field;
use halo2_proofs::circuit::{AssignedCell, Layouter};
use halo2_proofs::plonk::{Advice, Column, Error};
use std::convert::TryInto;

// TODO: should do proper base conv here
pub(crate) fn apply_absorb<F: Field>(
    add: &AddConfig<F>,
    layouter: &mut impl Layouter<F>,
    next_input_col: Column<Advice>,
    state: &[AssignedCell<F, F>; 25],
    next_input: &[Option<F>; NEXT_INPUTS_LANES],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let next_input_b9 = layouter.assign_region(
        || "next input words",
        |mut region| {
            let mut next_input_b9: Vec<AssignedCell<F, F>> = vec![];
            for (offset, input) in next_input.iter().enumerate() {
                let cell = region.assign_advice(
                    || "next input words",
                    next_input_col,
                    offset,
                    || {
                        Ok(input
                            .map(|input| {
                                let input = f_to_biguint(input);
                                let input = convert_b2_to_b9(
                                    *input.to_u64_digits().first().unwrap_or(&0u64),
                                );
                                biguint_to_f(&input)
                            })
                            .unwrap_or(F::zero()))
                    },
                )?;
                next_input_b9.push(cell);
            }
            Ok(next_input_b9)
        },
    )?;

    let mut out_state: Vec<AssignedCell<F, F>> = vec![];
    for (i, input) in next_input_b9.iter().enumerate() {
        let out_lane =
            add.add_advice_mul_const(layouter, state[i].clone(), input.clone(), F::from(A4))?;
        out_state.push(out_lane);
    }
    for i in NEXT_INPUTS_LANES..25 {
        out_state.push(state[i].clone());
    }
    Ok(out_state.try_into().unwrap())
}
