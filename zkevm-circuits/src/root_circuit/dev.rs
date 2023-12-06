use super::{aggregate, AggregationConfig, Halo2Loader, KzgSvk, Snark, SnarkWitness, LIMBS};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::{ff::Field as Halo2Field, serde::SerdeObject},
    plonk::{Circuit, ConstraintSystem, Error},
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
pub struct TestAggregationCircuit<'a, M: MultiMillerLoop, As> {
    svk: KzgSvk<M>,
    snarks: Vec<SnarkWitness<'a, M::G1Affine>>,
    instances: Vec<M::Scalar>,
    _marker: PhantomData<As>,
}

impl<'a, M: MultiMillerLoop, As> TestAggregationCircuit<'a, M, As>
where
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
    /// Create an Aggregation circuit with aggregated accumulator computed.
    /// Returns `None` if any given snark is invalid.
    pub fn new(
        params: &ParamsKZG<M>,
        snarks: impl IntoIterator<Item = Snark<'a, M::G1Affine>>,
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
    pub fn instances(&self) -> Vec<Vec<M::Scalar>> {
        vec![self.instances.clone()]
    }
}

impl<'a, M: MultiMillerLoop, As> Circuit<M::Scalar> for TestAggregationCircuit<'a, M, As>
where
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
            snarks: self
                .snarks
                .iter()
                .map(SnarkWitness::without_witnesses)
                .collect(),
            instances: vec![M::Scalar::ZERO; self.instances.len()],
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

        let (instances, accumulator_limbs) = layouter.assign_region(
            || "Aggregate snarks",
            |mut region| {
                config.named_column_in_region(&mut region);
                let ctx = RegionCtx::new(region, 0);
                let (instances, accumulator_limbs, _, _) =
                    config.aggregate::<M, As>(ctx, &self.svk, self.snarks.clone())?;
                let instances = instances
                    .iter()
                    .flatten()
                    .map(|instance| instance.assigned().to_owned())
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
