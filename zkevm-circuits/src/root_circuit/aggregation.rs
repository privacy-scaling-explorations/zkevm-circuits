use eth_types::Field;
use halo2::circuit::Region;
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
    verifier::{
        self,
        plonk::{PlonkProof, PlonkProtocol},
        SnarkVerifier,
    },
};
use std::{io, iter, rc::Rc};

use super::UserChallenge;

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
/// `LoadedScalar` with hardcoded `EccChip`.
pub type LoadedScalar<'a, C> = Scalar<'a, C, EccChip<C>>;
/// `PoseidonTranscript` with hardcoded parameter with 128-bits security.
pub type PoseidonTranscript<C, S> =
    transcript::halo2::PoseidonTranscript<C, NativeLoader, S, T, RATE, R_F, R_P>;

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
    /// protocol
    pub protocol: &'a PlonkProtocol<C>,
    /// instance
    pub instances: Value<&'a Vec<Vec<C::Scalar>>>,
    /// proof
    pub proof: Value<&'a [u8]>,
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

    /// named columns in region
    pub fn named_column_in_region<F: Field>(&self, region: &mut Region<'_, F>) {
        // annotate advices columns of `main_gate`. We can't annotate fixed_columns of
        // `main_gate` bcs there is no methods exported.
        for (i, col) in self.main_gate_config.advices().iter().enumerate() {
            region.name_column(|| format!("ROOT_main_gate_{}", i), *col);
        }
    }

    /// Aggregate witnesses into challenge and return
    #[allow(clippy::type_complexity)]
    pub fn aggregate_user_challenges<'c, M, As>(
        &self,
        loader: Rc<Halo2Loader<'c, M::G1Affine>>,
        user_challenges: Option<&UserChallenge>,
        proofs: Vec<PlonkProof<M::G1Affine, Rc<Halo2Loader<'c, M::G1Affine>>, As>>,
    ) -> Result<Vec<LoadedScalar<'c, M::G1Affine>>, Error>
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

        // Verify the cheap part and get accumulator (left-hand and right-hand side of
        // pairing) of individual proof.
        let witnesses = proofs
            .iter()
            .flat_map(|proof| {
                user_challenges
                    .map(|user_challenges| {
                        user_challenges
                            .column_indexes
                            .iter()
                            .map(|col| &proof.witnesses[col.index()])
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default()
            })
            .collect_vec();

        let empty_proof = Vec::new();
        let mut transcript = PoseidonTranscript::new(&loader, Value::known(empty_proof.as_slice()));
        witnesses.iter().for_each(|rwtable_col_ec_point| {
            transcript.common_ec_point(rwtable_col_ec_point).unwrap();
        });
        let num_challenges = user_challenges
            .map(|user_challenges| user_challenges.num_challenges)
            .unwrap_or_default();

        Ok((0..num_challenges)
            .map(|_| transcript.squeeze_challenge())
            .collect_vec())
    }

    /// Aggregate snarks into a single accumulator and decompose it into
    /// `4 * LIMBS` limbs.
    /// Returns assigned instances of snarks and aggregated accumulator limbs.
    #[allow(clippy::type_complexity)]
    pub fn aggregate<'a, 'c, M, As>(
        &self,
        ctx: RegionCtx<'c, M::Scalar>,
        svk: &KzgSvk<M>,
        snarks: &[SnarkWitness<'a, M::G1Affine>],
    ) -> Result<
        (
            Vec<Vec<Scalar<'c, M::G1Affine, EccChip<M::G1Affine>>>>,
            Vec<AssignedCell<M::Scalar, M::Scalar>>,
            Rc<Halo2Loader<'c, M::G1Affine>>,
            Vec<PlonkProof<M::G1Affine, Rc<Halo2Loader<'c, M::G1Affine>>, As>>,
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
        let ecc_chip = self.ecc_chip::<M::G1Affine>();
        let loader = Halo2Loader::<'c, _>::new(ecc_chip, ctx);

        type PoseidonTranscript<'a, C, S> =
            transcript::halo2::PoseidonTranscript<C, Rc<Halo2Loader<'a, C>>, S, T, RATE, R_F, R_P>;

        let mut plonk_svp = vec![];
        // Verify the cheap part and get accumulator (left-hand and right-hand side of
        // pairing) of individual proof.
        // Verify the cheap part and get accumulator (left-hand and right-hand side of
        // pairing) of individual proof.
        let (instances, accumulators) = snarks
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
                let accumulators =
                    PlonkSuccinctVerifier::verify(svk, &protocol, &instances, &proof).unwrap();
                plonk_svp.push(proof);
                (instances, accumulators)
            })
            .collect_vec()
            .into_iter()
            .unzip::<_, _, Vec<_>, Vec<_>>();

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
            .iter()
            .map(|instances| {
                instances
                    .iter()
                    .flat_map(|instances| {
                        instances
                            .iter()
                            .map(|instance| instance.to_owned())
                            .collect_vec()
                    })
                    .collect_vec()
            })
            .collect_vec();

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

        Ok((instances, accumulator_limbs, loader, plonk_svp))
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
