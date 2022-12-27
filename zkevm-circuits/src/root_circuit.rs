//! The Root circuit implementation.
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use itertools::Itertools;
use maingate::MainGateInstructions;
use snark_verifier::{util::arithmetic::MultiMillerLoop, verifier::plonk::PlonkProtocol};
use std::iter;

mod aggregation;

pub use aggregation::{
    aggregate, AggregationConfig, EccChip, Halo2Loader, KzgAs, KzgDk, KzgSvk,
    PlonkSuccinctVerifier, PlonkVerifier, PoseidonTranscript, Snark, SnarkWitness, BITS, LIMBS,
};
pub use snark_verifier::system::halo2::{compile, Config};

#[cfg(any(feature = "test", test))]
pub use aggregation::TestAggregationCircuit;

/// RootCircuit for aggregating SuperCircuit into a much smaller proof.
pub struct RootCircuit<'a, M: MultiMillerLoop> {
    svk: KzgSvk<M>,
    snark: SnarkWitness<'a, M::G1Affine>,
    instances: Vec<M::Scalar>,
}

impl<'a, M: MultiMillerLoop> RootCircuit<'a, M> {
    /// Create a `RootCircuit` with accumulator computed given a `SuperCircuit`
    /// proof and its instances. Returns `None` if given proof is invalid.
    pub fn new(
        params: &ParamsKZG<M>,
        super_circuit_protocol: &'a PlonkProtocol<M::G1Affine>,
        super_circuit_instances: Value<&'a Vec<Vec<M::Scalar>>>,
        super_circuit_proof: Value<&'a [u8]>,
    ) -> Option<Self> {
        let mut instances = Some(Vec::new());
        super_circuit_instances
            .as_ref()
            .zip(super_circuit_proof.as_ref())
            .map(|(super_circuit_instances, super_circuit_proof)| {
                let snark = Snark::new(
                    super_circuit_protocol,
                    super_circuit_instances,
                    super_circuit_proof,
                );
                instances = aggregate::<M>(params, [snark]).map(|accumulator_limbs| {
                    iter::empty()
                        // Propagate `SuperCircuit`'s instances
                        .chain(super_circuit_instances.iter().flatten().cloned())
                        // Output aggregated accumulator limbs
                        .chain(accumulator_limbs)
                        .collect_vec()
                });
            });

        instances.map(|instances| Self {
            svk: KzgSvk::<M>::new(params.get_g()[0]),
            snark: SnarkWitness::new(
                super_circuit_protocol,
                super_circuit_instances,
                super_circuit_proof,
            ),
            instances,
        })
    }

    /// Returns accumulator indices in instance columns, which will be in
    /// the last `4 * LIMBS` rows of instance column in `MainGate`.
    pub fn accumulator_indices(&self) -> Vec<(usize, usize)> {
        let offset = self.snark.protocol().num_instance.iter().sum::<usize>();
        (offset..).map(|idx| (0, idx)).take(4 * LIMBS).collect()
    }

    /// Returns number of instance
    pub fn num_instance(&self) -> Vec<usize> {
        vec![self.snark.protocol().num_instance.iter().sum::<usize>() + 4 * LIMBS]
    }

    /// Returns instances
    pub fn instances(&self) -> Vec<Vec<M::Scalar>> {
        vec![self.instances.clone()]
    }
}

impl<'a, M: MultiMillerLoop> Circuit<M::Scalar> for RootCircuit<'a, M> {
    type Config = AggregationConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            svk: self.svk,
            snark: self.snark.without_witnesses(),
            instances: vec![M::Scalar::zero(); self.instances.len()],
        }
    }

    fn configure(meta: &mut ConstraintSystem<M::Scalar>) -> Self::Config {
        AggregationConfig::configure::<M::G1Affine>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<M::Scalar>,
    ) -> Result<(), Error> {
        config.load_table(&mut layouter)?;
        let (instances, accumulator_limbs) =
            config.aggregate::<M>(&mut layouter, &self.svk, [self.snark])?;

        // Constrain equality to instance values
        let main_gate = config.main_gate();
        for (row, limb) in instances
            .into_iter()
            .flatten()
            .flatten()
            .chain(accumulator_limbs)
            .enumerate()
        {
            main_gate.expose_public(layouter.namespace(|| ""), limb, row)?;
        }

        Ok(())
    }
}

mod application {
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
        poly::Rotation,
    };
    use rand::rngs::OsRng;
    use rand::RngCore;

    #[derive(Clone, Copy)]
    pub struct StandardPlonkConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        q_a: Column<Fixed>,
        q_b: Column<Fixed>,
        q_c: Column<Fixed>,
        q_ab: Column<Fixed>,
        constant: Column<Fixed>,
        #[allow(dead_code)]
        instance: Column<Instance>,
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
            let [a, b, c] = [(); 3].map(|_| meta.advice_column());
            let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
            let instance = meta.instance_column();

            [a, b, c].map(|column| meta.enable_equality(column));

            meta.create_gate(
                "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
                |meta| {
                    let [a, b, c] =
                        [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let instance = meta.query_instance(instance, Rotation::cur());
                    Some(
                        q_a * a.clone()
                            + q_b * b.clone()
                            + q_c * c
                            + q_ab * a * b
                            + constant
                            + instance,
                    )
                },
            );

            StandardPlonkConfig {
                a,
                b,
                c,
                q_a,
                q_b,
                q_c,
                q_ab,
                constant,
                instance,
            }
        }
    }

    #[derive(Clone, Default)]
    pub struct StandardPlonk(Fr);

    impl StandardPlonk {
        pub fn rand<R: RngCore>(mut rng: R) -> Self {
            Self(Fr::from(rng.next_u32() as u64))
        }

        pub fn num_instance() -> Vec<usize> {
            vec![1]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            vec![vec![self.0]]
        }

        pub fn build() -> Result<(u32, Self, Vec<Vec<Fr>>, Vec<Fr>), Error> {
            let standPlonk = StandardPlonk::rand(OsRng);
            let instances = standPlonk.instances();
            return Ok((8, standPlonk, instances, vec![]));
        }
    }

    impl Circuit<Fr> for StandardPlonk {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            meta.set_minimum_degree(4);
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "",
                |mut region| {
                    region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                    region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fr::one()))?;

                    region.assign_advice(|| "", config.a, 1, || Value::known(-Fr::from(5)))?;
                    for (idx, column) in (1..).zip([
                        config.q_a,
                        config.q_b,
                        config.q_c,
                        config.q_ab,
                        config.constant,
                    ]) {
                        region.assign_fixed(|| "", column, 1, || Value::known(Fr::from(idx)))?;
                    }

                    let a = region.assign_advice(|| "", config.a, 2, || Value::known(Fr::one()))?;
                    a.copy_advice(|| "", &mut region, config.b, 3)?;
                    a.copy_advice(|| "", &mut region, config.c, 4)?;

                    Ok(())
                },
            )
        }
    }
}

#[cfg(test)]
mod test {
    use super::application::StandardPlonk;
    use crate::{
        root_circuit::{compile, Config, PoseidonTranscript, RootCircuit},
        super_circuit::{super_circuit_tests::sampl_block, SuperCircuit},
    };
    use halo2_proofs::{
        circuit::Value,
        dev::MockProver,
        halo2curves::bn256::Bn256,
        plonk::{create_proof, keygen_pk, keygen_vk},
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverGWC,
        },
    };
    use itertools::Itertools;
    use rand::rngs::OsRng;

    // #[ignore = "Due to high memory requirement"]
    #[test]
    fn test_root_circuit() {
        let (params, protocol, proof, instance) = {
            // Preprocess
            let (k, circuit, instance, _) =
                // SuperCircuit::<_, 1, 32, 256>::build(sampl_block()).unwrap();
                StandardPlonk::build().unwrap();

            let params = ParamsKZG::<Bn256>::setup(k, OsRng);
            let pk = keygen_pk(&params, keygen_vk(&params, &circuit).unwrap(), &circuit).unwrap();
            let protocol = compile(
                &params,
                pk.get_vk(),
                Config::kzg()
                    .with_num_instance(instance.iter().map(|instances| instances.len()).collect()),
            );

            // Create proof
            let proof = {
                let mut transcript = PoseidonTranscript::new(Vec::new());
                create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                    &params,
                    &pk,
                    &[circuit],
                    &[&instance.iter().map(Vec::as_slice).collect_vec()],
                    OsRng,
                    &mut transcript,
                )
                .unwrap();
                transcript.finalize()
            };

            (params, protocol, proof, instance)
        };

        let root_circuit = RootCircuit::new(
            &params,
            &protocol,
            Value::known(&instance),
            Value::known(&proof),
        )
        .unwrap();
        assert_eq!(
            MockProver::run(26, &root_circuit, root_circuit.instances())
                .unwrap()
                .verify_par(),
            Ok(())
        );
    }
}
