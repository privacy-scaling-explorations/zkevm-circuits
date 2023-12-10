//! The Root circuit implementation.
use eth_types::Field;
use halo2_proofs::{
    arithmetic::Field as Halo2Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::serde::SerdeObject,
    plonk::{Any, Circuit, Column, ConstraintSystem, Error},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use itertools::Itertools;
use maingate::{MainGateInstructions, RegionCtx};

use snark_verifier::{
    pcs::{
        kzg::{KzgAccumulator, KzgAsProvingKey, KzgAsVerifyingKey, KzgDecidingKey},
        AccumulationDecider, AccumulationScheme, AccumulationSchemeProver,
        PolynomialCommitmentScheme,
    },
    util::arithmetic::MultiMillerLoop,
    verifier::plonk::PlonkProtocol,
};
use std::{marker::PhantomData, rc::Rc};

mod aggregation;

#[cfg(any(test, feature = "test-circuits"))]
mod dev;
#[cfg(test)]
mod test;

#[cfg(feature = "test-circuits")]
pub use self::RootCircuit as TestRootCircuit;

#[cfg(any(feature = "test-circuits", test))]
pub use dev::TestAggregationCircuit;

pub use aggregation::{
    aggregate, AggregationConfig, EccChip, Gwc, Halo2Loader, KzgDk, KzgSvk, PlonkSuccinctVerifier,
    PlonkVerifier, PoseidonTranscript, Shplonk, Snark, SnarkWitness, BITS, LIMBS,
};
pub use snark_verifier::{
    loader::native::NativeLoader,
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
};

/// SuperCircuitInstance is to demystifying supercircuit instance to meaningful name.
#[derive(Clone)]
struct SuperCircuitInstance<T> {
    // chunk_ctx
    pub chunk_index: T,
    pub chunk_index_next: T,
    pub total_chunk: T,
    pub initial_rwc: T,
    pub end_rwc: T,

    // pi circuit
    pub pi_digest_lo: T,
    pub pi_digest_hi: T,

    // state circuit
    pub sc_permu_alpha: T,
    pub sc_permu_gamma: T,
    pub sc_rwtable_row_prev_fingerprint: T,
    pub sc_rwtable_row_next_fingerprint: T,
    pub sc_rwtable_prev_fingerprint: T,
    pub sc_rwtable_next_fingerprint: T,

    // evm circuit
    pub ec_permu_alpha: T,
    pub ec_permu_gamma: T,
    pub ec_rwtable_row_prev_fingerprint: T,
    pub ec_rwtable_row_next_fingerprint: T,
    pub ec_rwtable_prev_fingerprint: T,
    pub ec_rwtable_next_fingerprint: T,
}

impl<T: Clone + Copy> SuperCircuitInstance<T> {
    /// Construct `SnarkInstance` with vector
    pub fn new(instances: impl IntoIterator<Item = T>) -> Self {
        let raw_instances = instances.into_iter().collect_vec();
        assert_eq!(raw_instances.len(), 19);
        Self {
            chunk_index: raw_instances[0],
            total_chunk: raw_instances[1],
            initial_rwc: raw_instances[2],
            chunk_index_next: raw_instances[3],
            end_rwc: raw_instances[4],
            pi_digest_lo: raw_instances[5],
            pi_digest_hi: raw_instances[6],
            sc_permu_alpha: raw_instances[7],
            sc_permu_gamma: raw_instances[8],
            sc_rwtable_row_prev_fingerprint: raw_instances[9],
            sc_rwtable_row_next_fingerprint: raw_instances[10],
            sc_rwtable_prev_fingerprint: raw_instances[11],
            sc_rwtable_next_fingerprint: raw_instances[12],
            ec_permu_alpha: raw_instances[13],
            ec_permu_gamma: raw_instances[14],
            ec_rwtable_row_prev_fingerprint: raw_instances[15],
            ec_rwtable_row_next_fingerprint: raw_instances[16],
            ec_rwtable_prev_fingerprint: raw_instances[17],
            ec_rwtable_next_fingerprint: raw_instances[18],
        }
    }
}

/// UserChallange
pub struct UserChallenge {
    /// column_indexes
    pub column_indexes: Vec<Column<Any>>,
    /// num_challenges
    pub num_challenges: usize,
}

/// RootCircuit for aggregating SuperCircuit into a much smaller proof.
#[derive(Clone)]
pub struct RootCircuit<'a, M: MultiMillerLoop, As> {
    svk: KzgSvk<M>,
    snark: SnarkWitness<'a, M::G1Affine>,
    instance: Vec<M::Scalar>,
    _marker: PhantomData<As>,
}

impl<'a, M, As> RootCircuit<'a, M, As>
where
    M: MultiMillerLoop,
    M::G1Affine: SerdeObject,
    M::G2Affine: SerdeObject,
    M::Scalar: Field,
    As: PolynomialCommitmentScheme<
            M::G1Affine,
            NativeLoader,
            VerifyingKey = KzgSvk<M>,
            Output = KzgAccumulator<M::G1Affine, NativeLoader>,
        > + AccumulationSchemeProver<
            M::G1Affine,
            Accumulator = KzgAccumulator<M::G1Affine, NativeLoader>,
            ProvingKey = KzgAsProvingKey<M::G1Affine>,
        > + AccumulationDecider<M::G1Affine, NativeLoader, DecidingKey = KzgDecidingKey<M>>,
{
    /// Create a `RootCircuit` with accumulator computed given a `SuperCircuit`
    /// proof and its instance. Returns `None` if given proof is invalid.
    /// TODO support multiple snark proof aggregation
    pub fn new(
        params: &ParamsKZG<M>,
        super_circuit_protocol: &'a PlonkProtocol<M::G1Affine>,
        super_circuit_instances: Value<&'a Vec<Vec<M::Scalar>>>,
        super_circuit_proof: Value<&'a [u8]>,
        user_challenges: Option<&'a UserChallenge>,
    ) -> Result<Self, snark_verifier::Error> {
        let num_instances = super_circuit_protocol.num_instance.iter().sum::<usize>();

        // compute real instance value
        let (flatten_super_circuit_instances, accumulator_limbs) = {
            let (mut instance, mut accumulator_limbs) = (
                vec![M::Scalar::ZERO; num_instances],
                Ok(vec![M::Scalar::ZERO; 4 * LIMBS]),
            );
            super_circuit_instances
                .as_ref()
                .zip(super_circuit_proof.as_ref())
                .map(|(super_circuit_instances, super_circuit_proof)| {
                    let snark = Snark::new(
                        super_circuit_protocol,
                        super_circuit_instances,
                        super_circuit_proof,
                    );
                    accumulator_limbs = aggregate::<M, As>(params, [snark])
                        .map(|accumulator_limbs| accumulator_limbs.to_vec());
                    instance = super_circuit_instances
                        .iter()
                        .flatten()
                        .cloned()
                        .collect_vec()
                });
            (instance, accumulator_limbs?)
        };

        debug_assert_eq!(flatten_super_circuit_instances.len(), num_instances);
        let mut flatten_instance =
            exposed_instances(&SuperCircuitInstance::new(flatten_super_circuit_instances));
        flatten_instance.extend(accumulator_limbs);

        Ok(Self {
            svk: KzgSvk::<M>::new(params.get_g()[0]),
            snark: SnarkWitness::new(
                super_circuit_protocol,
                super_circuit_instances,
                user_challenges,
                super_circuit_proof,
            ),
            instance: flatten_instance,
            _marker: PhantomData,
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

    /// Returns instance
    pub fn instance(&self) -> Vec<Vec<M::Scalar>> {
        vec![self.instance.clone()]
    }
}

impl<'a, M, As> Circuit<M::Scalar> for RootCircuit<'a, M, As>
where
    M: MultiMillerLoop,
    M::Scalar: Field,
    for<'b> As: PolynomialCommitmentScheme<
            M::G1Affine,
            Rc<Halo2Loader<'b, M::G1Affine>>,
            VerifyingKey = KzgSvk<M>,
            Output = KzgAccumulator<M::G1Affine, Rc<Halo2Loader<'b, M::G1Affine>>>,
        > + AccumulationScheme<
            M::G1Affine,
            Rc<Halo2Loader<'b, M::G1Affine>>,
            Accumulator = KzgAccumulator<M::G1Affine, Rc<Halo2Loader<'b, M::G1Affine>>>,
            VerifyingKey = KzgAsVerifyingKey,
        >,
{
    type Config = AggregationConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            svk: self.svk,
            snark: self.snark.without_witnesses(),
            instance: vec![M::Scalar::ZERO; self.instance.len()],
            _marker: PhantomData,
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
        let key = &self.svk;
        let (instances, accumulator_limbs) = layouter.assign_region(
            || "Aggregate snarks",
            |mut region| {
                config.named_column_in_region(&mut region);
                let ctx = RegionCtx::new(region, 0);
                let (loaded_instances, accumulator_limbs, loader, proofs) =
                    config.aggregate::<M, As>(ctx, &key.clone(), [self.snark])?;

                // aggregate user challenge for rwtable permutation challenge
                let (alpha, gamma) = {
                    let mut challenges = config.aggregate_user_challenges::<M, As>(
                        loader.clone(),
                        self.snark.user_challenges(),
                        proofs,
                    )?;
                    (challenges.remove(0), challenges.remove(0))
                };

                // convert vector instances SuperCircuitInstance struct
                let supercircuit_instances = loaded_instances
                    .iter()
                    .map(SuperCircuitInstance::new)
                    .collect::<Vec<SuperCircuitInstance<_>>>();

                // constraint first and last chunk
                supercircuit_instances
                    .first()
                    .zip(supercircuit_instances.last())
                    .map(|(first_chunk, _last)| {
                        // `last.sc_rwtable_next_fingerprint ==
                        // last.ec_rwtable_next_fingerprint` will be checked inside super circuit so
                        // here no need to checked
                        // Other field in last instances already be checked in chunk
                        // continuity

                        // define 0, 1, total_chunk as constant
                        let (zero_const, one_const, total_chunk_const) = {
                            let zero_const = loader
                                .scalar_chip()
                                .assign_constant(&mut loader.ctx_mut(), M::Scalar::from(0))
                                .unwrap();
                            let one_const = loader
                                .scalar_chip()
                                .assign_constant(&mut loader.ctx_mut(), M::Scalar::from(1))
                                .unwrap();
                            let total_chunk_const = loader
                                .scalar_chip()
                                .assign_constant(&mut loader.ctx_mut(), M::Scalar::from(1))
                                .unwrap();
                            (zero_const, one_const, total_chunk_const)
                        };

                        // `first.sc_rwtable_row_prev_fingerprint ==
                        // first.ec_rwtable_row_prev_fingerprint` will be checked inside circuit
                        vec![
                            // chunk ctx
                            (first_chunk.chunk_index.assigned(), &zero_const),
                            (first_chunk.total_chunk.assigned(), &total_chunk_const),
                            // rwc
                            (first_chunk.initial_rwc.assigned(), &one_const),
                            // constraint permutation fingerprint
                            // challenge: alpha
                            (first_chunk.sc_permu_alpha.assigned(), &alpha.assigned()),
                            (first_chunk.ec_permu_alpha.assigned(), &alpha.assigned()),
                            // challenge: gamma
                            (first_chunk.sc_permu_gamma.assigned(), &gamma.assigned()),
                            (first_chunk.ec_permu_gamma.assigned(), &gamma.assigned()),
                            // fingerprint
                            (
                                first_chunk.ec_rwtable_prev_fingerprint.assigned(),
                                &one_const,
                            ),
                            (
                                first_chunk.sc_rwtable_prev_fingerprint.assigned(),
                                &one_const,
                            ),
                        ]
                        .iter()
                        .for_each(|(a, b)| {
                            loader
                                .scalar_chip()
                                .assert_equal(&mut loader.ctx_mut(), a, b)
                                .unwrap();
                        });

                        first_chunk
                    })
                    .expect("error");

                // constraint consistency between chunk
                supercircuit_instances.iter().tuple_windows().for_each(
                    |(instance_i, instance_i_plus_one)| {
                        vec![
                            (
                                instance_i.chunk_index_next.assigned(),
                                instance_i_plus_one.chunk_index.assigned(),
                            ),
                            (
                                instance_i.total_chunk.assigned(),
                                instance_i_plus_one.total_chunk.assigned(),
                            ),
                            (
                                instance_i.end_rwc.assigned(),
                                instance_i_plus_one.initial_rwc.assigned(),
                            ),
                            (
                                instance_i.pi_digest_lo.assigned(),
                                instance_i_plus_one.pi_digest_lo.assigned(),
                            ),
                            (
                                instance_i.pi_digest_hi.assigned(),
                                instance_i_plus_one.pi_digest_hi.assigned(),
                            ),
                            // state circuit
                            (
                                instance_i.sc_permu_alpha.assigned(),
                                instance_i_plus_one.sc_permu_alpha.assigned(),
                            ),
                            (
                                instance_i.sc_permu_gamma.assigned(),
                                instance_i_plus_one.sc_permu_gamma.assigned(),
                            ),
                            (
                                instance_i.sc_rwtable_row_next_fingerprint.assigned(),
                                instance_i_plus_one
                                    .sc_rwtable_row_prev_fingerprint
                                    .assigned(),
                            ),
                            (
                                instance_i.sc_rwtable_next_fingerprint.assigned(),
                                instance_i_plus_one.sc_rwtable_prev_fingerprint.assigned(),
                            ),
                            // evm circuit
                            (
                                instance_i.ec_permu_alpha.assigned(),
                                instance_i_plus_one.ec_permu_alpha.assigned(),
                            ),
                            (
                                instance_i.ec_permu_gamma.assigned(),
                                instance_i_plus_one.ec_permu_gamma.assigned(),
                            ),
                            (
                                instance_i.ec_rwtable_next_fingerprint.assigned(),
                                instance_i_plus_one.ec_rwtable_prev_fingerprint.assigned(),
                            ),
                            (
                                instance_i.ec_rwtable_row_next_fingerprint.assigned(),
                                instance_i_plus_one
                                    .ec_rwtable_row_prev_fingerprint
                                    .assigned(),
                            ),
                        ]
                        .iter()
                        .for_each(|(a, b)| {
                            loader
                                .scalar_chip()
                                .assert_equal(&mut loader.ctx_mut(), a, b)
                                .unwrap();
                        });
                    },
                );

                Ok((
                    exposed_instances(supercircuit_instances.first().unwrap())
                        .iter()
                        .map(|instance| instance.assigned().to_owned())
                        .collect_vec(),
                    accumulator_limbs,
                ))
            },
        )?;

        // Constrain equality to instance values
        let main_gate = config.main_gate();
        for (row, limb) in instances.into_iter().chain(accumulator_limbs).enumerate() {
            main_gate.expose_public(layouter.namespace(|| ""), limb, row)?;
        }

        Ok(())
    }
}

/// get instances to expose
fn exposed_instances<T: Copy>(supercircuit_instances: &SuperCircuitInstance<T>) -> Vec<T> {
    vec![
        // pi circuit
        supercircuit_instances.pi_digest_lo,
        supercircuit_instances.pi_digest_hi,
    ]
}
