use super::{
    aggregate, AggregationConfig, Halo2Loader, KzgSvk, Snark, SnarkWitness, UserChallenge, LIMBS,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::{ff::Field as Halo2Field, serde::SerdeObject, CurveAffine, CurveExt},
    plonk::{Circuit, ConstraintSystem, Error, Error::InvalidInstances},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use itertools::Itertools;
use maingate::{MainGateInstructions, RegionCtx};
use snark_verifier::{
    loader::native::NativeLoader,
    pcs::{
        kzg::*, AccumulationDecider, AccumulationScheme, AccumulationSchemeProver,
        PolynomialCommitmentScheme,
    },
    util::arithmetic::MultiMillerLoop,
};
use std::{iter, marker::PhantomData, rc::Rc};

/// Aggregation circuit for testing purpose.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct TestAggregationCircuit<'a, M: MultiMillerLoop, As>
where
    M::G1Affine: CurveAffine,
{
    svk: KzgSvk<M>,
    snarks: Vec<SnarkWitness<'a, M::G1Affine>>,
    user_challenge: Option<(UserChallenge, Vec<M::G1Affine>, Vec<M::Fr>)>,
    instances: Vec<M::Fr>,
    _marker: PhantomData<As>,
}

impl<'a, M, As> TestAggregationCircuit<'a, M, As>
where
    M: MultiMillerLoop,
    M::Fr: Field,
    M::G1: CurveExt<AffineExt = M::G1Affine, ScalarExt = M::Fr>,
    M::G1Affine: SerdeObject + CurveAffine<ScalarExt = M::Fr, CurveExt = M::G1>,
    M::G2Affine: SerdeObject + CurveAffine,
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
    /// Create an Aggregation circuit with aggregated accumulator computed.
    /// Returns `None` if any given snark is invalid.
    #[allow(clippy::type_complexity)]
    pub fn new(
        params: &ParamsKZG<M>,
        snarks: impl IntoIterator<Item = Snark<'a, M::G1Affine>>,
        user_challenge: Option<(UserChallenge, Vec<M::G1Affine>, Vec<M::Fr>)>,
    ) -> Result<Self, snark_verifier::Error> {
        let snarks = snarks.into_iter().collect_vec();

        let accumulator_limbs = aggregate::<M, As>(params, snarks.clone())?;
        let instances = iter::empty()
            // Propagate aggregated snarks' instances
            .chain(
                snarks
                    .iter()
                    .flat_map(|snark| snark.instances.clone())
                    .flatten(),
            )
            // Output aggregated accumulator
            .chain(accumulator_limbs)
            .collect_vec();

        Ok(Self {
            svk: KzgSvk::<M>::new(params.get_g()[0]),
            user_challenge,
            snarks: snarks.into_iter().map_into().collect(),
            instances,
            _marker: PhantomData,
        })
    }

    /// Returns accumulator indices in instance columns, which will be in
    /// the last 4 * LIMBS rows of MainGate's instance column.
    pub fn accumulator_indices(&self) -> Vec<(usize, usize)> {
        (self.instances.len() - 4 * LIMBS..)
            .map(|idx| (0, idx))
            .take(4 * LIMBS)
            .collect()
    }

    /// Returns number of instance
    pub fn num_instance(&self) -> Vec<usize> {
        vec![self.instances.len()]
    }

    /// Returns instances
    pub fn instances(&self) -> Vec<Vec<M::Fr>> {
        vec![self.instances.clone()]
    }
}

impl<'a, M: MultiMillerLoop, As> Circuit<M::Fr> for TestAggregationCircuit<'a, M, As>
where
    M::Fr: Field,
    M::G1Affine: CurveAffine<ScalarExt = M::Fr>,
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
            user_challenge: self.user_challenge.clone(),
            snarks: self
                .snarks
                .iter()
                .map(SnarkWitness::without_witnesses)
                .collect(),
            instances: vec![M::Fr::ZERO; self.instances.len()],
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<M::Fr>) -> Self::Config {
        AggregationConfig::configure::<M::G1Affine>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<M::Fr>,
    ) -> Result<(), Error> {
        config.load_table(&mut layouter)?;

        let (instances, accumulator_limbs) = layouter.assign_region(
            || "Aggregate snarks",
            |mut region| {
                config.named_column_in_region(&mut region);
                let ctx = RegionCtx::new(region, 0);
                let (instances, accumulator_limbs, loader, proofs) =
                    config.aggregate::<M, As>(ctx, &self.svk, &self.snarks)?;

                // aggregate user challenge for rwtable permutation challenge
                let user_challenge = self
                    .user_challenge
                    .as_ref()
                    .map(|(challenge, _, _)| challenge);
                let (challenges, commitments) = config.aggregate_user_challenges::<M, As>(
                    loader.clone(),
                    user_challenge,
                    proofs,
                )?;
                if !challenges.is_empty() {
                    let Some((_, expected_commitments, expected_challenges)) =
                        self.user_challenge.as_ref()
                    else {
                        return Err(InvalidInstances);
                    };
                    // check commitment equality
                    let expected_commitments_loaded = expected_commitments
                        .iter()
                        .map(|expected_commitment| {
                            loader.ecc_chip().assign_point(
                                &mut loader.ctx_mut(),
                                Value::known(*expected_commitment),
                            )
                        })
                        .collect::<Result<Vec<_>, Error>>()?;
                    expected_commitments_loaded
                        .iter()
                        .zip(commitments.iter())
                        .try_for_each(|(expected_commitment, commitment)| {
                            loader.ecc_chip().assert_equal(
                                &mut loader.ctx_mut(),
                                expected_commitment,
                                &commitment.assigned(),
                            )
                        })?;

                    // check challenge equality
                    let expected_challenges_loaded = expected_challenges
                        .iter()
                        .map(|value| loader.assign_scalar(Value::known(*value)))
                        .collect::<Vec<_>>();
                    expected_challenges_loaded
                        .iter()
                        .zip(challenges.iter())
                        .try_for_each(|(expected_challenge, challenge)| {
                            loader.scalar_chip().assert_equal(
                                &mut loader.ctx_mut(),
                                &expected_challenge.assigned(),
                                &challenge.assigned(),
                            )
                        })?;
                }

                let instances = instances
                    .iter()
                    .flat_map(|instances| {
                        instances
                            .iter()
                            .map(|instance| instance.assigned().to_owned())
                    })
                    .collect_vec();
                Ok((instances, accumulator_limbs))
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
