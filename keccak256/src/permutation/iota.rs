use crate::arith_helpers::{convert_b2_to_b13, convert_b2_to_b9, A4};
use crate::common::{PERMUTATION, ROUND_CONSTANTS};
use crate::gate_helpers::biguint_to_f;
use crate::permutation::add::AddConfig;
use eth_types::Field;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::plonk::Error;
use itertools::Itertools;
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub struct IotaConfig<F> {
    add: AddConfig<F>,
    round_constant_b13: F,
    a4_times_round_constants_b9: [F; PERMUTATION],
}

impl<F: Field> IotaConfig<F> {
    /// Iota step adds a round constant to the first lane.
    ///
    /// We enable the gate to handle 3 different cases:
    ///
    /// The first case takes place in the first 23 rounds, the prover MUST add
    /// the `A4` times round constant in base 9. We enforce it by requiring the
    /// flag equal to one.
    ///
    /// The second the third cases happen in the 24-th
    /// round. It depends if prover wants to absorb new input or not, which is
    /// indicated by the flag.
    ///
    /// If prover doesn't want to absorb new input,
    /// then add `A4 * round_constant_b9` as the previous 23-th round did.
    ///
    /// Otherwise, apply the round constant in base 13 to the state, which has
    /// been mixed with new input and converted form base 9 to base 13.
    pub fn configure(add: AddConfig<F>) -> Self {
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
            add,
            round_constant_b13,
            a4_times_round_constants_b9,
        }
    }

    /// The first 23 rounds. (No mixing logic involved).
    ///
    /// Applies IotaB9 steady-step logic.
    /// It consists of: `new_lane_00 - (lane00 * ROUND_CTANTS[round]) == 0`.
    pub fn assign_round_b9(
        &self,
        layouter: &mut impl Layouter<F>,
        lane00: AssignedCell<F, F>,
        round: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add
            .add_fixed(layouter, lane00, self.a4_times_round_constants_b9[round])
    }

    /// The 24-th round. Copy the flag `no_mixing` here.
    ///
    /// If `no_mixing` is true: add `A4 * round_constant_b9`
    /// Otherwise, do nothing and return the orignal lane value in the next cell
    pub fn assign_b9_last_round(
        &self,
        layouter: &mut impl Layouter<F>,
        lane00: AssignedCell<F, F>,
        flag: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add.conditional_add(
            layouter,
            lane00,
            flag,
            self.a4_times_round_constants_b9[PERMUTATION - 1],
        )
    }

    /// The 24-th round. Copy the flag `mixing` here.
    ///
    /// If `mixing` is true: add round constant in base 13.
    /// Otherwise, do nothing and return the orignal lane value in the next cell
    pub fn assign_round_b13(
        &self,
        layouter: &mut impl Layouter<F>,
        lane00: AssignedCell<F, F>,
        flag: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add
            .conditional_add(layouter, lane00, flag, self.round_constant_b13)
    }
}
