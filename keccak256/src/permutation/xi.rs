use crate::arith_helpers::{A1, A2, A3};
use crate::permutation::generic::GenericConfig;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use itertools::Itertools;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::*;
    use crate::common::*;
    use crate::gate_helpers::biguint_to_f;
    use crate::keccak_arith::*;
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::pairing::bn256::Fr as Fp;
    use halo2_proofs::plonk::{Advice, Column, ConstraintSystem, Error};
    use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use itertools::Itertools;
    use std::marker::PhantomData;

    #[test]
    fn test_xi_gate() {
        #[derive(Clone, Debug)]
        struct MyConfig<F> {
            lane: Column<Advice>,
            generic: GenericConfig<F>,
        }

        impl<F: Field> MyConfig<F> {
            pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
                let advices: [Column<Advice>; 3] = (0..3)
                    .map(|_| {
                        let column = meta.advice_column();
                        meta.enable_equality(column);
                        column
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let fixed = meta.fixed_column();

                let lane = advices[0];
                let generic = GenericConfig::configure(meta, advices, fixed);
                Self { lane, generic }
            }
        }
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            _marker: PhantomData<F>,
        }

        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                // this column is required by `constrain_constant`
                let constant = meta.fixed_column();
                meta.enable_constant(constant);
                Self::Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let in_state = layouter.assign_region(
                    || "Wittnes & assignation",
                    |mut region| {
                        // Witness `state`
                        let in_state: [AssignedCell<F, F>; 25] = {
                            let mut state: Vec<AssignedCell<F, F>> = Vec::with_capacity(25);
                            for (offset, val) in self.in_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    config.lane,
                                    offset,
                                    || Ok(*val),
                                )?;
                                state.push(cell)
                            }
                            state.try_into().unwrap()
                        };
                        Ok(in_state)
                    },
                )?;

                let out_state = assign_xi(&config.generic, &mut layouter, &in_state)?;

                layouter.assign_region(
                    || "Check outstate",
                    |mut region| {
                        for (assigned, value) in out_state.iter().zip(self.out_state.iter()) {
                            region.constrain_constant(assigned.cell(), value)?;
                        }
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        let input1: State = [
            [1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b9(input1[x][y]);
            in_state[5 * x + y] = biguint_to_f(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::xi(&in_biguint);
        let mut out_state: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = biguint_to_f(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<Fp> {
            in_state,
            out_state,
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover = MockProver::<Fp>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
