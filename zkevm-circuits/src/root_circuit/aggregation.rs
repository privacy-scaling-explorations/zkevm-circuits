use eth_types::Field;
use halo2::plonk::{Any, Column};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    halo2curves::{
        group::prime::PrimeCurveAffine, pairing::Engine, serde::SerdeObject, CurveAffine,
    },
    plonk::{ConstraintSystem, Error},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use itertools::Itertools;
use rand::{rngs::StdRng, SeedableRng};
use snark_verifier::{
    loader::{
        self,
        halo2::{
            halo2_wrong_ecc::{self, integer::rns::Rns, maingate::*, EccConfig},
            Scalar,
        },
        native::NativeLoader,
    },
    pcs::{
        kzg::*, AccumulationDecider, AccumulationScheme, AccumulationSchemeProver,
        PolynomialCommitmentScheme,
    },
    system::halo2::transcript,
    util::{
        arithmetic::{fe_to_limbs, MultiMillerLoop},
        transcript::Transcript,
    },
    verifier::{self, plonk::PlonkProtocol, SnarkVerifier},
};
use std::{io, iter, rc::Rc};

use crate::util::unwrap_value;

/// Number of limbs to decompose a elliptic curve base field element into.
pub const LIMBS: usize = 4;
/// Number of bits of each decomposed limb.
pub const BITS: usize = 68;

/// KZG accumulation scheme with GWC19 multiopen.
pub type Gwc<M> = KzgAs<M, Gwc19>;
/// KZG accumulation scheme with BDFG21 multiopen.
pub type Shplonk<M> = KzgAs<M, Bdfg21>;
/// KZG succinct verifying key
pub type KzgSvk<M> = KzgSuccinctVerifyingKey<<M as Engine>::G1Affine>;
/// KZG deciding key
pub type KzgDk<M> = KzgDecidingKey<M>;
/// Plonk succinct verifier with `KzgAs`
pub type PlonkSuccinctVerifier<As> = verifier::plonk::PlonkSuccinctVerifier<As>;
/// Plonk verifier with `KzgAs` and `LimbsEncoding<LIMBS, BITS>`.
pub type PlonkVerifier<As> = verifier::plonk::PlonkVerifier<As, LimbsEncoding<LIMBS, BITS>>;

const T: usize = 5;
const RATE: usize = 4;
const R_F: usize = 8;
const R_P: usize = 60;

/// `BaseFieldEccChip` with hardcoded `LIMBS` and `BITS` serving as `EccChip`
/// for `Halo2Loader`.
pub type EccChip<C> = halo2_wrong_ecc::BaseFieldEccChip<C, LIMBS, BITS>;
/// `Halo2Loader` with hardcoded `EccChip`.
pub type Halo2Loader<'a, C> = loader::halo2::Halo2Loader<'a, C, EccChip<C>>;
/// `PoseidonTranscript` with hardcoded parameter with 128-bits security.
pub type PoseidonTranscript<C, S> =
    transcript::halo2::PoseidonTranscript<C, NativeLoader, S, T, RATE, R_F, R_P>;

/// SuperCircuitInstance is to demystifying supercircuit instance to meaningful name.
#[derive(Clone)]
pub struct SuperCircuitInstance<T> {
    pub chunk_index: T,
    pub chunk_index_next: T,
    pub total_chunk: T,
    pub initial_rwc: T,
    pub end_rwc: T,
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

    raw_instances: Vec<T>,
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
            raw_instances,
        }
    }

    fn raw_instances(&self) -> &Vec<T> {
        &self.raw_instances
    }
}
/// Snark contains the minimal information for verification
#[derive(Clone, Copy)]
pub struct Snark<'a, C: CurveAffine> {
    protocol: &'a PlonkProtocol<C>,
    pub(crate) instances: &'a Vec<Vec<C::Scalar>>,
    proof: &'a [u8],
}

impl<'a, C: CurveAffine> Snark<'a, C> {
    /// Construct `Snark` with each field.
    pub fn new(
        protocol: &'a PlonkProtocol<C>,
        instances: &'a Vec<Vec<C::Scalar>>,
        proof: &'a [u8],
    ) -> Self {
        Self {
            protocol,
            instances,
            proof,
        }
    }
}

impl<'a, C: CurveAffine> From<Snark<'a, C>> for SnarkWitness<'a, C> {
    fn from(snark: Snark<'a, C>) -> Self {
        Self {
            protocol: snark.protocol,
            instances: Value::known(snark.instances),
            proof: Value::known(snark.proof),
        }
    }
}

/// SnarkWitness
#[derive(Clone, Copy)]
pub struct SnarkWitness<'a, C: CurveAffine> {
    protocol: &'a PlonkProtocol<C>,
    instances: Value<&'a Vec<Vec<C::Scalar>>>,
    proof: Value<&'a [u8]>,
}

impl<'a, C: CurveAffine> SnarkWitness<'a, C> {
    /// Construct `SnarkWitness` with each field.
    pub fn new(
        protocol: &'a PlonkProtocol<C>,
        instances: Value<&'a Vec<Vec<C::Scalar>>>,
        proof: Value<&'a [u8]>,
    ) -> Self {
        Self {
            protocol,
            instances,
            proof,
        }
    }

    /// Returns `SnarkWitness` with all witness as `Value::unknown()`.
    pub fn without_witnesses(&self) -> Self {
        SnarkWitness {
            protocol: self.protocol,
            instances: Value::unknown(),
            proof: Value::unknown(),
        }
    }

    /// Returns protocol as reference.
    pub fn protocol(&self) -> &PlonkProtocol<C> {
        self.protocol
    }

    /// Returns proof as reference.
    pub fn proof(&self) -> Value<&[u8]> {
        self.proof
    }

    fn loaded_instances<'b>(
        &self,
        loader: &Rc<Halo2Loader<'b, C>>,
    ) -> Vec<Vec<Scalar<'b, C, EccChip<C>>>> {
        self.instances
            .transpose_vec(self.protocol.num_instance.len())
            .into_iter()
            .zip(self.protocol.num_instance.iter())
            .map(|(instances, num_instance)| {
                instances
                    .transpose_vec(*num_instance)
                    .into_iter()
                    .map(|instance| loader.assign_scalar(instance.copied()))
                    .collect_vec()
            })
            .collect_vec()
    }
}

/// Aggregation configuration.
#[derive(Clone)]
pub struct AggregationConfig {
    /// MainGateConfig
    pub main_gate_config: MainGateConfig,
    /// RangeConfig
    pub range_config: RangeConfig,
}

impl AggregationConfig {
    /// Configure for `MainGate` and `RangeChip` with corresponding fixed lookup
    /// table.
    pub fn configure<C: CurveAffine>(meta: &mut ConstraintSystem<C::Scalar>) -> Self {
        let main_gate_config = MainGate::<C::Scalar>::configure(meta);
        let range_config = RangeChip::<C::Scalar>::configure(
            meta,
            &main_gate_config,
            vec![BITS / LIMBS],
            Rns::<C::Base, C::Scalar, LIMBS, BITS>::construct().overflow_lengths(),
        );
        Self {
            main_gate_config,
            range_config,
        }
    }

    /// Returns `MainGate`.
    pub fn main_gate<F: Field>(&self) -> MainGate<F> {
        MainGate::new(self.main_gate_config.clone())
    }

    /// Returns `RangeChip`.
    pub fn range_chip<F: Field>(&self) -> RangeChip<F> {
        RangeChip::new(self.range_config.clone())
    }

    /// Returns `EccChip`.
    pub fn ecc_chip<C: CurveAffine>(&self) -> EccChip<C> {
        EccChip::new(EccConfig::new(
            self.range_config.clone(),
            self.main_gate_config.clone(),
        ))
    }

    /// Load fixed lookup table for `RangeChip`
    pub fn load_table<F: Field>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.range_chip().load_table(layouter)
    }

    /// Aggregate snarks into a single accumulator and decompose it into
    /// `4 * LIMBS` limbs.
    /// Returns assigned instances of snarks and aggregated accumulator limbs.
    /// TODO Fine tune or generalize design to avoid hacky pass rwtable_columns
    #[allow(clippy::type_complexity)]
    pub fn aggregate<'a, M, As>(
        &self,
        layouter: &mut impl Layouter<M::Scalar>,
        svk: &KzgSvk<M>,
        snarks: impl IntoIterator<Item = SnarkWitness<'a, M::G1Affine>>,
        rwtable_columns: Vec<Column<Any>>,
    ) -> Result<
        (
            Vec<AssignedCell<M::Scalar, M::Scalar>>,
            Vec<AssignedCell<M::Scalar, M::Scalar>>,
        ),
        Error,
    >
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
        type PoseidonTranscript<'a, C, S> =
            transcript::halo2::PoseidonTranscript<C, Rc<Halo2Loader<'a, C>>, S, T, RATE, R_F, R_P>;

        // get rwtable witness column index
        let rwtable_witness_colindex = rwtable_columns
            .iter()
            .map(|col| col.index())
            .collect::<Vec<usize>>();

        let snarks = snarks.into_iter().collect_vec();
        layouter.assign_region(
            || "Aggregate snarks",
            |mut region| {
                // annotate advices columns of `main_gate`. We can't annotate fixed_columns of
                // `main_gate` bcs there is no methods exported.
                for (i, col) in self.main_gate_config.advices().iter().enumerate() {
                    region.name_column(|| format!("ROOT_main_gate_{}", i), *col);
                }

                let ctx = RegionCtx::new(region, 0);

                let ecc_chip = self.ecc_chip::<M::G1Affine>();
                let loader = Halo2Loader::new(ecc_chip, ctx);

                // Verify the cheap part and get accumulator (left-hand and right-hand side of
                // pairing) of individual proof.
                let (instance_witnesses, accumulators) = snarks
                    .iter()
                    .map(|snark| {
                        let protocol = snark.protocol.loaded(&loader);
                        let instances = snark.loaded_instances(&loader);
                        let mut transcript = PoseidonTranscript::new(&loader, snark.proof());
                        let proof = PlonkSuccinctVerifier::<As>::read_proof(
                            svk,
                            &protocol,
                            &instances,
                            &mut transcript,
                        )
                        .unwrap();

                        let rwtable_col_witness = rwtable_witness_colindex
                            .iter()
                            .map(|col_index| proof.witnesses[*col_index].clone())
                            .collect::<Vec<_>>();

                        let accumulators =
                            PlonkSuccinctVerifier::verify(svk, &protocol, &instances, &proof)
                                .unwrap();
                        ((instances, rwtable_col_witness), accumulators)
                    })
                    .collect_vec()
                    .into_iter()
                    .unzip::<_, _, Vec<_>, Vec<_>>();

                // convert vector instances SuperCircuitInstance struct
                let supercircuit_instances = instance_witnesses
                    .iter()
                    .map(|x| SuperCircuitInstance::new(x.0.iter().flatten().collect::<Vec<_>>()))
                    .collect::<Vec<SuperCircuitInstance<_>>>();

                // get all column commitment loaded ec points (witness of rw_table from all
                // snark proof, then absorb them into fresh transcript to squeeze to
                // get challenge alpha', following by absorb alpha' and squeeze to get challenge
                // gamma'. At the end, constraint alpha', gamma' field value equal to alpha,
                // gamma appear at public input instances by simply invoke loaded field value
                // equality: `alpha' - alpha = 0` and `gamma' - gamma = 0`
                // collect rwtable witness
                let rwtable_witness = instance_witnesses
                    .iter()
                    .flat_map(|x| x.1.clone())
                    .collect::<Vec<_>>();
                let empty_proof = Vec::new();
                let mut transcript =
                    PoseidonTranscript::new(&loader, Value::known(empty_proof.as_slice()));
                rwtable_witness.iter().for_each(|rwtable_col_ec_point| {
                    transcript.common_ec_point(rwtable_col_ec_point).unwrap();
                });
                // derive challenge alpha and gamma
                let alpha = transcript.squeeze_challenge();
                let gamma = transcript.squeeze_challenge();

                // constraint first and last chunk
                let instances = supercircuit_instances
                    .first()
                    .zip(supercircuit_instances.last())
                    .map(|(first, _last)| {
                        // `last.sc_rwtable_next_fingerprint ==
                        // last.ec_rwtable_next_fingerprint` will be checked inside super circuit so
                        // here no need to checked
                        // Other field in last instances already be checked in below chunk
                        // continuity

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
                        let sc_initial_fingerprint = loader
                            .scalar_chip()
                            .assign_constant(
                                &mut loader.ctx_mut(),
                                unwrap_value(
                                    first
                                        .sc_rwtable_prev_fingerprint
                                        .assigned()
                                        .to_owned()
                                        .value()
                                        .map(|v| *v),
                                ),
                            )
                            .unwrap();
                        let ec_initial_fingerprint = loader
                            .scalar_chip()
                            .assign_constant(
                                &mut loader.ctx_mut(),
                                unwrap_value(
                                    first
                                        .ec_rwtable_prev_fingerprint
                                        .assigned()
                                        .to_owned()
                                        .value()
                                        .map(|v| *v),
                                ),
                            )
                            .unwrap();

                        // `first.sc_rwtable_row_prev_fingerprint ==
                        // first.ec_rwtable_row_prev_fingerprint` will be checked inside circuit
                        vec![
                            // chunk ctx
                            (first.chunk_index.assigned().to_owned(), zero_const),
                            (first.total_chunk.assigned().to_owned(), total_chunk_const),
                            // rwc
                            (first.initial_rwc.assigned().to_owned(), one_const),
                            // constraint permutation fingerprint
                            // challenge: alpha
                            (
                                first.sc_permu_alpha.assigned().to_owned(),
                                alpha.assigned().to_owned(),
                            ),
                            (
                                first.ec_permu_alpha.assigned().to_owned(),
                                alpha.assigned().to_owned(),
                            ),
                            // challenge: gamma
                            (
                                first.sc_permu_gamma.assigned().to_owned(),
                                gamma.assigned().to_owned(),
                            ),
                            (
                                first.ec_permu_gamma.assigned().to_owned(),
                                gamma.assigned().to_owned(),
                            ),
                            // fingerprint
                            (
                                first.ec_rwtable_prev_fingerprint.assigned().to_owned(),
                                ec_initial_fingerprint,
                            ),
                            (
                                first.sc_rwtable_prev_fingerprint.assigned().to_owned(),
                                sc_initial_fingerprint,
                            ),
                        ]
                        .iter()
                        .for_each(|(a, b)| {
                            loader
                                .scalar_chip()
                                .assert_equal(&mut loader.ctx_mut(), a, b)
                                .unwrap();
                        });

                        first
                    })
                    .expect("error");

                // constraint consistency between chunk
                let _ = supercircuit_instances.iter().tuple_windows().inspect(
                    |(instance_i, instance_i_plus_one)| {
                        vec![
                            (
                                instance_i.chunk_index_next.assigned().to_owned(),
                                instance_i_plus_one.chunk_index.assigned().to_owned(),
                            ),
                            (
                                instance_i.total_chunk.assigned().to_owned(),
                                instance_i_plus_one.total_chunk.assigned().to_owned(),
                            ),
                            (
                                instance_i.end_rwc.assigned().to_owned(),
                                instance_i_plus_one.initial_rwc.assigned().to_owned(),
                            ),
                            (
                                instance_i.pi_digest_lo.assigned().to_owned(),
                                instance_i_plus_one.pi_digest_lo.assigned().to_owned(),
                            ),
                            (
                                instance_i.pi_digest_hi.assigned().to_owned(),
                                instance_i_plus_one.pi_digest_hi.assigned().to_owned(),
                            ),
                            // state circuit
                            (
                                instance_i.sc_permu_alpha.assigned().to_owned(),
                                instance_i_plus_one.sc_permu_alpha.assigned().to_owned(),
                            ),
                            (
                                instance_i.sc_permu_gamma.assigned().to_owned(),
                                instance_i_plus_one.sc_permu_gamma.assigned().to_owned(),
                            ),
                            (
                                instance_i
                                    .sc_rwtable_row_next_fingerprint
                                    .assigned()
                                    .to_owned(),
                                instance_i_plus_one
                                    .sc_rwtable_row_prev_fingerprint
                                    .assigned()
                                    .to_owned(),
                            ),
                            (
                                instance_i.sc_rwtable_next_fingerprint.assigned().to_owned(),
                                instance_i_plus_one
                                    .sc_rwtable_prev_fingerprint
                                    .assigned()
                                    .to_owned(),
                            ),
                            // evm circuit
                            (
                                instance_i.ec_permu_alpha.assigned().to_owned(),
                                instance_i_plus_one.ec_permu_alpha.assigned().to_owned(),
                            ),
                            (
                                instance_i.ec_permu_gamma.assigned().to_owned(),
                                instance_i_plus_one.ec_permu_gamma.assigned().to_owned(),
                            ),
                            (
                                instance_i.ec_rwtable_next_fingerprint.assigned().to_owned(),
                                instance_i_plus_one
                                    .ec_rwtable_prev_fingerprint
                                    .assigned()
                                    .to_owned(),
                            ),
                            (
                                instance_i
                                    .ec_rwtable_row_next_fingerprint
                                    .assigned()
                                    .to_owned(),
                                instance_i_plus_one
                                    .ec_rwtable_row_prev_fingerprint
                                    .assigned()
                                    .to_owned(),
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

                // Verify proof for accumulation of all accumulators into new one.
                let accumulator = {
                    let as_vk = Default::default();
                    let as_proof = Vec::new();
                    let accumulators = accumulators.into_iter().flatten().collect_vec();
                    let mut transcript =
                        PoseidonTranscript::new(&loader, Value::known(as_proof.as_slice()));
                    let proof = <As as AccumulationScheme<_, _>>::read_proof(
                        &as_vk,
                        &accumulators,
                        &mut transcript,
                    )
                    .unwrap();
                    <As as AccumulationScheme<_, _>>::verify(&as_vk, &accumulators, &proof).unwrap()
                };

                let instances = instances
                    .raw_instances()
                    .iter()
                    .map(|instance| instance.assigned().to_owned())
                    .collect();

                let accumulator_limbs = [accumulator.lhs, accumulator.rhs]
                    .iter()
                    .map(|ec_point| {
                        loader
                            .ecc_chip()
                            .assign_ec_point_to_limbs(&mut loader.ctx_mut(), ec_point.assigned())
                    })
                    .collect::<Result<Vec<_>, Error>>()?
                    .into_iter()
                    .flatten()
                    .collect();

                Ok((instances, accumulator_limbs))
            },
        )
    }
}

/// Aggregate snarks into a single accumulator and decompose it into
/// `4 * LIMBS` limbs.
/// Returns `None` if any given snarks is invalid.
pub fn aggregate<'a, M, As>(
    params: &ParamsKZG<M>,
    snarks: impl IntoIterator<Item = Snark<'a, M::G1Affine>>,
) -> Result<[M::Scalar; 4 * LIMBS], snark_verifier::Error>
where
    M: MultiMillerLoop,
    M::G1Affine: SerdeObject,
    M::G2Affine: SerdeObject,
    M::Scalar: Field,
    for<'b> As: PolynomialCommitmentScheme<
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
    let svk = KzgSvk::<M>::new(params.get_g()[0]);
    let dk = KzgDk::new(svk, params.g2(), params.s_g2());

    // Use the same logic of verifier to get accumulator (left-hand and right-hand
    // side of pairing) of individual proof.
    let accumulators = snarks
        .into_iter()
        .map(|snark| {
            let mut transcript = PoseidonTranscript::new(snark.proof);
            let proof = PlonkSuccinctVerifier::<As>::read_proof(
                &svk,
                snark.protocol,
                snark.instances,
                &mut transcript,
            )?;
            for commitment in iter::empty()
                .chain(snark.protocol.preprocessed.iter())
                .chain(proof.witnesses.iter())
                .chain(proof.quotients.iter())
            {
                if bool::from(commitment.is_identity()) {
                    return Err(snark_verifier::Error::Transcript(
                        io::ErrorKind::Other,
                        "Identity point in preprocessed or proof is not yet supported".to_string(),
                    ));
                }
            }
            PlonkSuccinctVerifier::verify(&svk, snark.protocol, snark.instances, &proof)
        })
        .try_collect::<_, Vec<_>, _>()?
        .into_iter()
        .flatten()
        .collect_vec();

    // Create proof for accumulation of all accumulators into new one.
    // In our case (KZG without zero-knowledge), it's no-ops since the verifier
    // could add up the accumulators into the new one itself in circuit.
    let accumulator = {
        let as_pk = Default::default();
        let rng = StdRng::from_seed(Default::default());
        let mut transcript = PoseidonTranscript::new(Vec::new());
        let accumulator = As::create_proof(&as_pk, &accumulators, &mut transcript, rng)?;
        assert!(transcript.finalize().is_empty());
        accumulator
    };
    As::decide(&dk, accumulator.clone())?;

    let KzgAccumulator { lhs, rhs } = accumulator;
    let accumulator_limbs = [lhs, rhs]
        .into_iter()
        .flat_map(|point| {
            let coordinates = point.coordinates().unwrap();
            [*coordinates.x(), *coordinates.y()]
        })
        .flat_map(fe_to_limbs::<_, _, LIMBS, BITS>)
        .collect_vec()
        .try_into()
        .unwrap();
    Ok(accumulator_limbs)
}

/// Contains TestAggregationCircuit to test whether aggregation is working for
/// any given inputs.
#[cfg(test)]
pub mod test {
    use crate::root_circuit::{
        aggregation::Gwc, PoseidonTranscript, Snark, TestAggregationCircuit,
    };
    use eth_types::Field;
    use halo2_proofs::{
        arithmetic::Field as Halo2Field,
        circuit::{floor_planner::V1, Layouter, Value},
        dev::{FailureLocation, MockProver, VerifyFailure},
        halo2curves::{
            bn256::{Bn256, Fr, G1Affine},
            CurveAffine,
        },
        plonk::{
            create_proof, keygen_pk, keygen_vk, Advice, Any, Circuit, Column, ConstraintSystem,
            Error, Fixed,
        },
        poly::{
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::ProverGWC,
            },
            Rotation,
        },
    };
    use itertools::Itertools;
    use rand::{rngs::OsRng, RngCore};
    use snark_verifier::{
        system::halo2::{compile, Config},
        verifier::plonk::PlonkProtocol,
    };
    use std::iter;

    #[derive(Clone)]
    pub struct SnarkOwned<C: CurveAffine> {
        protocol: PlonkProtocol<C>,
        instances: Vec<Vec<C::Scalar>>,
        proof: Vec<u8>,
    }

    impl<C: CurveAffine> SnarkOwned<C> {
        pub fn new(
            protocol: PlonkProtocol<C>,
            instances: Vec<Vec<C::Scalar>>,
            proof: Vec<u8>,
        ) -> Self {
            Self {
                protocol,
                instances,
                proof,
            }
        }

        pub fn as_snark(&self) -> Snark<C> {
            Snark {
                protocol: &self.protocol,
                instances: &self.instances,
                proof: &self.proof,
            }
        }
    }

    /// Configuration for `StandardPlonk`
    #[derive(Clone)]
    pub struct StandardPlonkConfig {
        selectors: [Column<Fixed>; 5],
        wires: [Column<Advice>; 3],
    }

    impl StandardPlonkConfig {
        /// Configure for `StandardPlonk`
        pub fn configure<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
            let [w_l, w_r, w_o] = [(); 3].map(|_| meta.advice_column());
            let [q_l, q_r, q_o, q_m, q_c] = [(); 5].map(|_| meta.fixed_column());
            let pi = meta.instance_column();
            [w_l, w_r, w_o].map(|column| meta.enable_equality(column));
            meta.create_gate(
                "q_l·w_l + q_r·w_r + q_o·w_o + q_m·w_l·w_r + q_c + pi = 0",
                |meta| {
                    let [w_l, w_r, w_o] =
                        [w_l, w_r, w_o].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_l, q_r, q_o, q_m, q_c] = [q_l, q_r, q_o, q_m, q_c]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let pi = meta.query_instance(pi, Rotation::cur());
                    Some(
                        q_l * w_l.clone()
                            + q_r * w_r.clone()
                            + q_o * w_o
                            + q_m * w_l * w_r
                            + q_c
                            + pi,
                    )
                },
            );
            StandardPlonkConfig {
                selectors: [q_l, q_r, q_o, q_m, q_c],
                wires: [w_l, w_r, w_o],
            }
        }
    }

    /// Standard plonk with few assignments for testing purpose.
    #[derive(Clone, Copy)]
    pub struct StandardPlonk<F>(F);

    impl<F: Field> StandardPlonk<F> {
        /// Create a `StandardPlonk` with random instnace.
        pub fn rand<R: RngCore>(mut rng: R) -> Self {
            Self(F::from(rng.next_u32() as u64))
        }

        /// Returns instances.
        pub fn instances(&self) -> Vec<Vec<F>> {
            vec![vec![self.0]]
        }
    }

    impl<F: Field> Circuit<F> for StandardPlonk<F> {
        type Config = StandardPlonkConfig;
        type FloorPlanner = V1;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            meta.set_minimum_degree(4);
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let [q_l, q_r, q_o, q_m, q_c] = config.selectors;
            let [w_l, w_r, w_o] = config.wires;
            layouter.assign_region(
                || "",
                |mut region| {
                    // Assign some non-zero values to make sure the advice/fixed columns have
                    // non-identity commitments.
                    let a = region.assign_advice(|| "", w_l, 0, || Value::known(self.0))?;
                    region.assign_fixed(|| "", q_l, 0, || Value::known(-F::ONE))?;
                    a.copy_advice(|| "", &mut region, w_r, 1)?;
                    a.copy_advice(|| "", &mut region, w_o, 2)?;
                    region.assign_advice(|| "", w_l, 3, || Value::known(-F::from(5)))?;
                    for (column, idx) in [q_l, q_r, q_o, q_m, q_c].iter().zip(1..) {
                        region.assign_fixed(|| "", *column, 3, || Value::known(F::from(idx)))?;
                    }
                    Ok(())
                },
            )
        }
    }

    /// Create random `StandardPlonk` and returns `Snark`s for them.
    pub fn rand_standard_plonk_snarks(
        params: &ParamsKZG<Bn256>,
        n: usize,
    ) -> Vec<SnarkOwned<G1Affine>> {
        // Preprocess
        let (pk, protocol) = {
            let standard_plonk = StandardPlonk(Fr::ZERO);
            let vk = keygen_vk(params, &standard_plonk).unwrap();
            let pk = keygen_pk(params, vk, &standard_plonk).unwrap();
            let protocol = compile(
                params,
                pk.get_vk(),
                Config::kzg().with_num_instance(
                    standard_plonk
                        .instances()
                        .iter()
                        .map(|instances| instances.len())
                        .collect(),
                ),
            );
            (pk, protocol)
        };

        // Create snarks
        iter::repeat_with(move || {
            let standard_plonk = StandardPlonk::<Fr>::rand(OsRng);
            let instances = standard_plonk.instances();
            let proof = {
                let mut transcript = PoseidonTranscript::new(Vec::new());
                create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                    params,
                    &pk,
                    &[standard_plonk],
                    &[&instances.iter().map(Vec::as_slice).collect_vec()],
                    OsRng,
                    &mut transcript,
                )
                .unwrap();
                transcript.finalize()
            };
            SnarkOwned::new(protocol.clone(), instances, proof)
        })
        .take(n)
        .collect()
    }

    #[test]
    fn test_standard_plonk_aggregation() {
        let params = ParamsKZG::<Bn256>::setup(8, OsRng);

        // Create Aggregation circuit and compute aggregated accumulator
        let snarks = rand_standard_plonk_snarks(&params, 2);
        let aggregation = TestAggregationCircuit::<Bn256, Gwc<_>>::new(
            &params,
            snarks.iter().map(SnarkOwned::as_snark),
        )
        .unwrap();
        let instances = aggregation.instances();
        assert_eq!(
            MockProver::run(21, &aggregation, instances)
                .unwrap()
                .verify_par(),
            Ok(())
        );
    }

    #[test]
    fn test_standard_plonk_aggregation_unmatched_instance() {
        let params = ParamsKZG::<Bn256>::setup(8, OsRng);

        // Create Aggregation circuit and compute aggregated accumulator
        let snarks = rand_standard_plonk_snarks(&params, 2);
        let aggregation = TestAggregationCircuit::<Bn256, Gwc<_>>::new(
            &params,
            snarks.iter().map(SnarkOwned::as_snark),
        )
        .unwrap();
        let mut instances = aggregation.instances();
        // Change the propagated inner snark's instance
        instances[0][0] += Fr::ONE;
        // Then expect the verification to fail
        assert_eq!(
            MockProver::run(21, &aggregation, instances)
                .unwrap()
                .verify_par(),
            Err(vec![
                VerifyFailure::Permutation {
                    column: (Any::advice(), 0).into(),
                    location: FailureLocation::InRegion {
                        region: (1, "Aggregate snarks").into(),
                        offset: 0
                    }
                },
                VerifyFailure::Permutation {
                    column: (Any::Instance, 0).into(),
                    location: FailureLocation::OutsideRegion { row: 0 }
                }
            ])
        );
    }
}
