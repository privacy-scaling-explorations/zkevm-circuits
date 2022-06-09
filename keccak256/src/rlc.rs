use std::marker::PhantomData;

use eth_types::Field;
use gadgets::expression::*;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct RlcConfig<F: Field, const N: usize> {
    q_enable: Selector,
    witness: [Column<Advice>; N],
    rlc: Column<Advice>,
    randomness: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: Field, const N: usize> RlcConfig<F, N> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        witness: [Column<Advice>; N],
        randomness: Column<Advice>,
        rlc: Column<Advice>,
    ) -> RlcConfig<F, N> {
        let q_enable = meta.selector();
        meta.create_gate("RLC check", |meta| {
            // Query witnesses to accumulate in the RLC
            let witness: [Expression<F>; N] =
                witness.map(|w| meta.query_advice(w, Rotation::cur()));
            let randomness = meta.query_advice(randomness, Rotation::cur());

            // Query resulting RLC result
            let result = meta.query_advice(rlc, Rotation::cur());

            let obtained_result = rlc::compose::<F, N>(&witness, randomness);
            let q_enable = meta.query_selector(q_enable);

            vec![q_enable * (obtained_result - result)]
        });

        RlcConfig {
            q_enable,
            witness,
            randomness,
            rlc,
            _marker: PhantomData,
        }
    }

    pub fn assign_rlc(
        &self,
        layouter: &mut impl Layouter<F>,
        witness: [AssignedCell<F, F>; N],
        randomness: AssignedCell<F, F>,
        rlc: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "RLC",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                witness
                    .iter()
                    .enumerate()
                    .map(|(idx, cell)| -> Result<_, _> {
                        cell.copy_advice(|| "RLC witness data", &mut region, self.witness[idx], 0)
                    })
                    .collect::<Result<Vec<_>, Error>>()?;

                randomness.copy_advice(|| "RLC randomness", &mut region, self.randomness, 0)?;

                // Assign RLC result
                rlc.copy_advice(|| "RLC result", &mut region, self.rlc, 0)?;
                Ok(())
            },
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod rlc_tests {
    use super::*;
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::pairing::bn256::Fr as Fp;
    use halo2_proofs::plonk::{ConstraintSystem, Error, Instance};
    use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use pretty_assertions::assert_eq;
    use std::convert::TryInto;

    struct MyCircuit<F, const N: usize> {
        witness: [F; N],
        randomness: F,
        rlc: F,
    }

    impl<F: Field, const N: usize> Default for MyCircuit<F, N> {
        fn default() -> Self {
            MyCircuit {
                witness: [F::zero(); N],
                randomness: F::zero(),
                rlc: F::zero(),
            }
        }
    }

    #[derive(Clone)]
    struct MyConfig<F: Field, const N: usize> {
        rlc_config: RlcConfig<F, N>,
        randomness: Column<Instance>,
        randomness_adv: Column<Advice>,
        witness: [Column<Advice>; N],
        rlc: Column<Advice>,
    }

    impl<F: Field, const N: usize> Circuit<F> for MyCircuit<F, N> {
        type Config = MyConfig<F, N>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let witness = [(); N].map(|_| meta.advice_column()).map(|col| {
                meta.enable_equality(col);
                col
            });

            let randomness = meta.instance_column();
            meta.enable_equality(randomness);

            let rlc = meta.advice_column();
            meta.enable_equality(rlc);

            let randomness_adv = meta.advice_column();
            meta.enable_equality(randomness_adv);

            let rlc_config = RlcConfig::configure(meta, witness, randomness_adv, rlc);

            MyConfig {
                rlc_config,
                randomness,
                randomness_adv,
                witness,
                rlc,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let offset: usize = 0;

            let witness = layouter.assign_region(
                || "Keccak round Wittnes & flag assignation",
                |mut region| {
                    // Witness `state`
                    let witness: [AssignedCell<F, F>; N] = {
                        let mut state: Vec<AssignedCell<F, F>> = Vec::with_capacity(N);
                        for (idx, val) in self.witness.iter().enumerate() {
                            let cell = region.assign_advice(
                                || "RLC witness",
                                config.witness[idx],
                                offset,
                                || Ok(*val),
                            )?;
                            state.push(cell)
                        }
                        state.try_into().unwrap()
                    };

                    Ok(witness)
                },
            )?;

            let rlc = layouter.assign_region(
                || "RLC result",
                |mut region| {
                    region.assign_advice(|| "RLC result", config.rlc, offset, || Ok(self.rlc))
                },
            )?;

            let randomness = layouter.assign_region(
                || "RLC randomness",
                |mut region| {
                    region.assign_advice_from_instance(
                        || "RLC randomness",
                        config.randomness,
                        0usize,
                        config.randomness_adv,
                        0usize,
                    )
                },
            )?;

            config
                .rlc_config
                .assign_rlc(&mut layouter, witness, randomness, rlc)?;

            Ok(())
        }
    }

    #[test]
    fn end_to_end() {
        const N: usize = 25;
        let witness = [Fp::one(); N];
        let og_randomness = Fp::from(2u64);
        let mut randomness = og_randomness.clone();
        let mut rlc = witness[0].clone();

        // Compute rlc
        for value in witness[1..].iter() {
            rlc = rlc + value.clone() * randomness.clone();
            randomness = randomness * og_randomness.clone();
        }

        let circuit = MyCircuit::<Fp, N> {
            witness,
            randomness,
            rlc,
        };

        // Correct result should pass the tests.
        let prover = MockProver::<Fp>::run(9, &circuit, vec![vec![og_randomness]]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        // Wrong randomness PI should make the test fail.
        let prover = MockProver::<Fp>::run(9, &circuit, vec![vec![Fp::from(25519u64)]]).unwrap();
        assert!(prover.verify().is_err());

        // Wrong RLC result should make the test fail.
        let circuit = MyCircuit::<Fp, N> {
            witness,
            randomness,
            rlc: Fp::from(999u64),
        };
        let prover = MockProver::<Fp>::run(9, &circuit, vec![vec![og_randomness]]).unwrap();
        assert!(prover.verify().is_err());
    }
}
