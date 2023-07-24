//! The Root circuit implementation.
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::bn256::{Bn256, Fr},
    plonk::{Circuit, ConstraintSystem, Error},
    poly::kzg::commitment::ParamsKZG,
};
use itertools::Itertools;
use maingate::{MainGateInstructions, RangeInstructions};
use snark_verifier_sdk::{CircuitExt, LIMBS};
use std::fmt;

pub use snark_verifier::system::halo2::{compile, Config};
use snark_verifier_sdk::{
    halo2::aggregation::{AccumulationSchemeSDK, AggregationCircuit, AggregationConfig},
    Snark,
};

// TODO: move this to snark-verifier-sdk
/// AggregationType is used to specify which accumulation scheme to use.
#[derive(Clone, Copy, Debug)]
pub enum AccumulationSchemeType {
    /// using GWC
    GwcType,
    /// using SHPLONK
    ShplonkType,
}

impl From<AccumulationSchemeType> for u64 {
    fn from(t: AccumulationSchemeType) -> u64 {
        match t {
            AccumulationSchemeType::GwcType => 0,
            AccumulationSchemeType::ShplonkType => 1,
        }
    }
}

impl From<u64> for AccumulationSchemeType {
    fn from(t: u64) -> AccumulationSchemeType {
        match t {
            0 => AccumulationSchemeType::GwcType,
            1 => AccumulationSchemeType::ShplonkType,
            _ => panic!("Invalid aggregation type"),
        }
    }
}

/// TaikoAggregationCircuit for aggregating various sub circuits into a smaller proof.
#[derive(Clone)]
pub struct TaikoAggregationCircuit<AS>
where
    AS: AccumulationSchemeSDK,
{
    aggregation_circuit: AggregationCircuit<AS>,
    input_snarks: Vec<Snark>,
}

impl<AS> TaikoAggregationCircuit<AS>
where
    AS: AccumulationSchemeSDK,
{
    /// Create a `TaikoAggregationCircuit` with accumulator computed by
    /// Snark array. Returns `None` if given proof is invalid.
    pub fn new(
        params: &ParamsKZG<Bn256>,
        snarks: impl IntoIterator<Item = Snark>,
    ) -> Result<Self, snark_verifier::Error> {
        let input_snarks = snarks.into_iter().collect_vec();
        Ok(Self {
            aggregation_circuit: AggregationCircuit::<AS>::new(params, input_snarks.clone()),
            input_snarks,
        })
    }

    /// Returns accumulator indices in instance columns, which will be in
    /// the last `4 * LIMBS` rows of instance column in `MainGate`.
    pub fn accumulator_indices(&self) -> Vec<(usize, usize)> {
        let total_instance_num = self.num_instance().iter().sum::<usize>();
        assert!(total_instance_num >= 4 * LIMBS);
        (total_instance_num - 4 * LIMBS..total_instance_num)
            .map(|idx| (0, idx))
            .collect()
    }

    /// Returns number of instance
    pub fn num_instance(&self) -> Vec<usize> {
        let prev_instance_num = self
            .input_snarks
            .iter()
            .map(|snark| snark.instances.iter().map(|s| s.len()).sum::<usize>())
            .sum::<usize>();
        vec![
            prev_instance_num
                + self
                    .aggregation_circuit
                    .num_instance()
                    .iter()
                    .sum::<usize>(),
        ]
    }

    /// Returns instance
    pub fn instance(&self) -> Vec<Vec<Fr>> {
        let acc_limbs = self.aggregation_circuit.instances();
        assert!(acc_limbs.len() == 1 && acc_limbs[0].len() == 4 * LIMBS);
        let prev_instance = self
            .input_snarks
            .iter()
            .flat_map(|s| s.instances.clone())
            .collect_vec();

        vec![prev_instance
            .into_iter()
            .chain(acc_limbs.into_iter())
            .flatten()
            .collect_vec()]
    }
}

impl<AS> fmt::Display for TaikoAggregationCircuit<AS>
where
    AS: AccumulationSchemeSDK,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Root circuit num_instance {:?}, instance: {:?})",
            self.num_instance(),
            self.instance()
        )
    }
}

impl<AS> CircuitExt<Fr> for TaikoAggregationCircuit<AS>
where
    AS: AccumulationSchemeSDK,
{
    fn num_instance(&self) -> Vec<usize> {
        self.num_instance()
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        self.instance()
    }
}

impl<AS> Circuit<Fr> for TaikoAggregationCircuit<AS>
where
    AS: AccumulationSchemeSDK,
{
    type Config = AggregationConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            aggregation_circuit: self.aggregation_circuit.without_witnesses(),
            input_snarks: self.input_snarks.clone(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        AggregationCircuit::<AS>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let main_gate = config.main_gate();
        let range_chip = config.range_chip();
        range_chip.load_table(&mut layouter)?;

        let (accumulator_limbs, prev_instances) = self
            .aggregation_circuit
            .aggregation_region(config, &mut layouter)?;

        let mut offset = 0;
        // Constrain equality to instance values
        for (row, limb) in prev_instances.into_iter().flatten().enumerate() {
            main_gate.expose_public(layouter.namespace(|| "prev instances"), limb, row)?;
            offset += 1;
        }

        for (idx, limb) in accumulator_limbs.into_iter().enumerate() {
            let row = idx + offset;
            main_gate.expose_public(layouter.namespace(|| "accumulate limbs"), limb, row)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::bn256::{Bn256, Fr},
        plonk::{
            keygen_pk, keygen_vk, Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance,
        },
        poly::{
            commitment::Params,
            kzg::multiopen::{ProverGWC, VerifierGWC},
            Rotation,
        },
    };
    use rand::RngCore;
    use rand_chacha::rand_core::OsRng;
    use snark_verifier_sdk::{
        halo2::{gen_proof, gen_srs},
        GWC,
    };

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
    }

    impl Circuit<Fr> for StandardPlonk {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

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

    fn gen_app_snark(params: &ParamsKZG<Bn256>) -> Snark {
        let circuit = StandardPlonk::rand(OsRng);

        let vk = keygen_vk(params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(params, vk, &circuit).expect("keygen_pk should not fail");

        let protocol = compile(
            params,
            pk.get_vk(),
            Config::kzg().with_num_instance(StandardPlonk::num_instance()),
        );

        let proof = gen_proof::<_, ProverGWC<_>, VerifierGWC<_>>(
            params,
            &pk,
            circuit.clone(),
            circuit.instances(),
            None::<(&str, &str)>,
        );
        Snark::new(protocol, circuit.instances(), proof)
    }

    #[test]
    fn test_simple_taiko_agg() {
        let k = 21;
        let params = gen_srs(k);
        let mut app_params = params.clone();
        app_params.downsize(k - 3);
        let snarks = (0..2).map(|_| gen_app_snark(&app_params)).collect_vec();

        let root_circuit = TaikoAggregationCircuit::<GWC>::new(&params, snarks).unwrap();
        assert_eq!(
            MockProver::run(k, &root_circuit, root_circuit.instance())
                .unwrap()
                .verify_par(),
            Ok(())
        );
    }
}
