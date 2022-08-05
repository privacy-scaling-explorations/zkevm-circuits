use crate::arith_helpers::{convert_b2_to_b13, convert_b2_to_b9, A4};
use crate::common::{PERMUTATION, ROUND_CONSTANTS};
use crate::gate_helpers::biguint_to_f;
use eth_types::Field;
use itertools::Itertools;

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
