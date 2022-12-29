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
#[derive(Clone)]
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
            let stand_plonk = StandardPlonk::rand(OsRng);
            let instances = stand_plonk.instances();
            return Ok((22, stand_plonk, instances, vec![]));
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
        halo2curves::bn256::{Bn256, Fq, Fr, G1Affine},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey,
        },
        poly::commitment::{Params, ParamsProver},
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        poly::VerificationStrategy,
        transcript::{EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer},
    };
    use itertools::Itertools;
    use rand::rngs::OsRng;
    use snark_verifier::{
        loader::{
            evm::{self, encode_calldata, Address, EvmLoader, ExecutorBuilder},
            native::NativeLoader,
        },
        pcs::kzg::{Gwc19, KzgAs, LimbsEncoding},
        pcs::{
            kzg::{KzgAccumulator, KzgSuccinctVerifyingKey, LimbsEncodingInstructions},
            AccumulationScheme, AccumulationSchemeProver,
        },
        system,
        system::halo2::transcript::evm::EvmTranscript,
        util::arithmetic::{fe_to_limbs, FieldExt},
        verifier::{self, plonk::PlonkProtocol, SnarkVerifier},
    };
    use std::{fs, io::Cursor, rc::Rc, time::Instant};

    const LIMBS: usize = 4;
    const BITS: usize = 68;

    type As = KzgAs<Bn256, Gwc19>;
    type PlonkSuccinctVerifier =
        verifier::plonk::PlonkSuccinctVerifier<As, LimbsEncoding<LIMBS, BITS>>;
    type PlonkVerifier = verifier::plonk::PlonkVerifier<As, LimbsEncoding<LIMBS, BITS>>;

    pub fn write_params(degree: usize, params: &ParamsKZG<Bn256>) -> Result<(), std::io::Error> {
        let dir = "./generated";
        fs::create_dir_all(dir).unwrap_or_else(|_| panic!("create {}", dir));
        let path = format!("{}/srs-{}", dir, degree);
        let mut file = fs::File::create(&path).unwrap_or_else(|_| panic!("create {}", &path));
        params.write(&mut file)
    }

    pub fn read_params(degree: usize) -> Result<ParamsKZG<Bn256>, std::io::Error> {
        let dir = "./generated";
        let path = format!("{}/srs-{}", dir, degree);
        let mut file = fs::File::open(&path)?;
        ParamsKZG::<Bn256>::read(&mut file)
    }

    pub fn get_circuit_params<const D: usize>(degree: usize) -> ParamsKZG<Bn256> {
        let mut params = if let Ok(params) = read_params(degree) {
            params
        } else {
            let params = ParamsKZG::<Bn256>::setup(degree as u32, OsRng);
            write_params(degree, &params).expect("write srs ok");
            params
        };

        if D > 0 {
            params.downsize(D as u32);
        }
        params
    }

    use std::fs::File;
    use std::io::Write as fwrite;

    fn gen_aggregation_evm_verifier(
        params: &ParamsKZG<Bn256>,
        vk: &VerifyingKey<G1Affine>,
        num_instance: Vec<usize>,
        accumulator_indices: Vec<(usize, usize)>,
    ) -> Vec<u8> {
        let protocol = compile(
            params,
            vk,
            Config::kzg()
                .with_num_instance(num_instance.clone())
                .with_accumulator_indices(Some(accumulator_indices)),
        );
        let vk = (params.get_g()[0], params.g2(), params.s_g2()).into();

        let loader = EvmLoader::new::<Fq, Fr>();
        let protocol = protocol.loaded(&loader);
        let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

        let instances = transcript.load_instances(num_instance);
        let proof = PlonkVerifier::read_proof(&vk, &protocol, &instances, &mut transcript).unwrap();
        PlonkVerifier::verify(&vk, &protocol, &instances, &proof).unwrap();

        File::create("./PlonkAggregationVerifier.sol")
            .expect("PlonkAggregationVerifier.sol")
            .write_all(&loader.yul_code().as_bytes())
            .expect("PlonkAggregationVerifier.sol");

        evm::compile_yul(&loader.yul_code())
    }

    fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
        let calldata = encode_calldata(&instances, &proof);
        let success = {
            let mut evm = ExecutorBuilder::default()
                .with_gas_limit(u64::MAX.into())
                .build();

            let caller = Address::from_low_u64_be(0xfe);
            let verifier = evm
                .deploy(caller, deployment_code.into(), 0.into())
                .address
                .unwrap();
            let result = evm.call_raw(caller, verifier, calldata.into(), 0.into());

            dbg!(result.gas_used);

            !result.reverted
        };
        assert!(success);
    }

    fn gen_proof<
        C: Circuit<Fr>,
        E: EncodedChallenge<G1Affine>,
        TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
        TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
    >(
        params: &ParamsKZG<Bn256>,
        pk: &ProvingKey<G1Affine>,
        circuit: C,
        instances: Vec<Vec<Fr>>,
    ) -> Vec<u8> {
        MockProver::run(params.k(), &circuit, instances.clone())
            .unwrap()
            .assert_satisfied();

        let instances = instances
            .iter()
            .map(|instances| instances.as_slice())
            .collect_vec();
        let proof = {
            let mut transcript = TW::init(Vec::new());
            create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, TW, _>(
                params,
                pk,
                &[circuit],
                &[instances.as_slice()],
                OsRng,
                &mut transcript,
            )
            .unwrap();
            transcript.finalize()
        };

        let accept = {
            let mut transcript = TR::init(Cursor::new(proof.clone()));
            VerificationStrategy::<_, VerifierGWC<_>>::finalize(
                verify_proof::<_, VerifierGWC<_>, _, TR, _>(
                    params.verifier_params(),
                    pk.get_vk(),
                    AccumulatorStrategy::new(params.verifier_params()),
                    &[instances.as_slice()],
                    &mut transcript,
                )
                .unwrap(),
            )
        };
        assert!(accept);

        proof
    }

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
        )
    }

    #[test]
    fn test_root_circuit_evm_verifier() {
        let mut start = Instant::now();
        let (params_app, params, protocol, proof, instance) = {
            // Preprocess
            let (k, circuit, instance, _) =
                // SuperCircuit::<_, 1, 32, 256>::build(sampl_block()).unwrap();
                StandardPlonk::build().unwrap();

            // let params = ParamsKZG::<Bn256>::setup(k, OsRng);
            let params = get_circuit_params::<0>(k as usize);
            let params_app = get_circuit_params::<10>(k as usize);
            let pk = keygen_pk(
                &params_app,
                keygen_vk(&params_app, &circuit).unwrap(),
                &circuit,
            )
            .unwrap();
            let protocol = compile(
                &params_app,
                pk.get_vk(),
                Config::kzg()
                    .with_num_instance(instance.iter().map(|instances| instances.len()).collect()),
            );

            // Create proof
            let proof = {
                let mut transcript = PoseidonTranscript::new(Vec::new());
                create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                    &params_app,
                    &pk,
                    &[circuit],
                    &[&instance.iter().map(Vec::as_slice).collect_vec()],
                    OsRng,
                    &mut transcript,
                )
                .unwrap();
                transcript.finalize()
            };

            (params_app, params, protocol, proof, instance)
        };

        let duration = start.elapsed();
        println!(
            "gen app proof elapsed in expensive_function() is: {:?}",
            duration
        );

        start = Instant::now();

        let root_circuit = RootCircuit::new(
            &params_app,
            &protocol,
            Value::known(&instance),
            Value::known(&proof),
        )
        .unwrap();

        let pk = keygen_pk(
            &params,
            keygen_vk(&params, &root_circuit).unwrap(),
            &root_circuit,
        )
        .unwrap();
        let duration = start.elapsed();
        println!(
            "root_circuit pk elapsed in expensive_function() is: {:?}",
            duration
        );

        start = Instant::now();
        let deployment_code = gen_aggregation_evm_verifier(
            &params,
            pk.get_vk(),
            root_circuit.num_instance(),
            root_circuit.accumulator_indices(),
        );

        let duration = start.elapsed();
        println!(
            "deployment_code elapsed in expensive_function() is: {:?}",
            duration
        );

        start = Instant::now();

        let proof = gen_proof::<
            _,
            _,
            EvmTranscript<G1Affine, _, _, _>,
            EvmTranscript<G1Affine, _, _, _>,
        >(&params, &pk, root_circuit.clone(), root_circuit.instances());
        let duration = start.elapsed();
        println!(
            "gen_proof elapsed in expensive_function() is: {:?}",
            duration
        );

        start = Instant::now();

        evm_verify(deployment_code, root_circuit.instances(), proof);

        let duration = start.elapsed();
        println!(
            "evm_verify elapsed in expensive_function() is: {:?}",
            duration
        );
    }
}
