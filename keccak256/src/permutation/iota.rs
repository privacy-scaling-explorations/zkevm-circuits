use crate::arith_helpers::{convert_b2_to_b13, convert_b2_to_b9, A4};
use crate::common::{PERMUTATION, ROUND_CONSTANTS};
use crate::gate_helpers::biguint_to_f;
use eth_types::Field;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use num_bigint::BigUint;
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub struct IotaConfig<F> {
    q_b9: Selector,
    q_b13: Selector,
    lane00: Column<Advice>,
    flag: Column<Advice>,
    round_constant: Column<Fixed>,
    round_constant_b13: F,
    round_constants_b9: [BigUint; PERMUTATION],
}

impl<F: Field> IotaConfig<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        lane00: Column<Advice>,
        flag: Column<Advice>,
        round_constant: Column<Fixed>,
    ) -> Self {
        let q_b9 = meta.selector();
        let q_b13 = meta.selector();
        meta.enable_equality(lane00);
        meta.enable_equality(flag);

        meta.create_gate("iota_b9 in steady state", |meta| {
            let q_b9 = meta.query_selector(q_b9);
            let lane00_next = meta.query_advice(lane00, Rotation::next());
            let lane00 = meta.query_advice(lane00, Rotation::cur());
            let round_constant = meta.query_fixed(round_constant, Rotation::cur());
            vec![q_b9 * (lane00_next - lane00 - round_constant)]
        });

        let round_constant_b13 =
            biguint_to_f::<F>(&convert_b2_to_b13(ROUND_CONSTANTS[PERMUTATION - 1]));

        meta.create_gate("iota_b13", |meta| {
            let q_b13 = meta.query_selector(q_b13);
            let flag = meta.query_advice(flag, Rotation::cur());

            let lane00_next = meta.query_advice(lane00, Rotation::cur());
            let lane00 = meta.query_advice(lane00, Rotation::cur());
            vec![q_b13 * (lane00_next - lane00 - flag * Expression::Constant(round_constant_b13))]
        });

        let round_constants_b9: [BigUint; 24] = ROUND_CONSTANTS
            .iter()
            .map(|&x| convert_b2_to_b9(x))
            .collect_vec()
            .try_into()
            .unwrap();
        Self {
            q_b9,
            q_b13,
            lane00,
            flag,
            round_constant,
            round_constant_b13,
            round_constants_b9,
        }
    }

    pub fn assign_round_b9(
        &self,
        layouter: &mut impl Layouter<F>,
        lane00: AssignedCell<F, F>,
        round: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "IotaB9",
            |mut region| {
                let offset = 0;
                self.q_b9.enable(&mut region, offset)?;
                lane00.copy_advice(|| "lane 00", &mut region, self.lane00, offset)?;

                let constant = A4 * self.round_constants_b9[round].clone();
                let constant = biguint_to_f::<F>(&constant);
                region.assign_fixed(
                    || "A4 * round_constant_b9",
                    self.round_constant,
                    offset,
                    || Ok(constant),
                )?;

                let offset = 1;
                region.assign_advice(
                    || "lane 00 + A4 * round_constant_b9",
                    self.lane00,
                    offset,
                    || Ok(constant + lane00.value().cloned().unwrap_or_default()),
                )
            },
        )
    }
    pub fn assign_round_b13(
        &self,
        layouter: &mut impl Layouter<F>,
        lane00: AssignedCell<F, F>,
        flag: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "IotaB9",
            |mut region| {
                let offset = 0;
                self.q_b13.enable(&mut region, offset)?;
                lane00.copy_advice(|| "lane 00", &mut region, self.lane00, offset)?;
                flag.copy_advice(|| "flag", &mut region, self.flag, offset)?;

                let offset = 1;
                region.assign_advice(
                    || "lane 00 + round_constant_b13",
                    self.lane00,
                    offset,
                    || {
                        let lane00 = lane00.value().cloned().unwrap_or_default();
                        let flag = flag.value().cloned().unwrap_or_default();
                        Ok(lane00 + flag * self.round_constant_b13)
                    },
                )
            },
        )
    }
}
