#![allow(unused_imports)]
use super::*;
use halo2_proofs::{
    dev::{MockProver, VerifyFailure},
    halo2curves::bn256::Fr,
};
use mock::{CORRECT_MOCK_TXS, MOCK_CHAIN_ID};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

// We define the PiTestCircuit as a wrapper over PiCircuit extended to take the
// generic const parameters MAX_TXS and MAX_CALLDATA.  This is necessary because
// the trait Circuit requires an implementation of `configure` that doesn't take
// any circuit parameters, and the PiCircuit defines gates that use rotations
// that depend on MAX_TXS and MAX_CALLDATA, so these two values are required
// during the configuration.
/// Test Circuit for PiCircuit
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
#[derive(Default, Clone)]
pub struct PiTestCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
    pub PiCircuit<F>,
);

#[cfg(any(feature = "test", test, feature = "test-circuits"))]
impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> SubCircuit<F>
    for PiTestCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    type Config = PiCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        assert_eq!(block.circuits_params.max_txs, MAX_TXS);
        assert_eq!(block.circuits_params.max_calldata, MAX_CALLDATA);

        Self(PiCircuit::new_from_block(block))
    }

    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        assert_eq!(block.circuits_params.max_txs, MAX_TXS);
        assert_eq!(block.circuits_params.max_calldata, MAX_CALLDATA);

        PiCircuit::min_num_rows_block(block)
    }

    /// Compute the public inputs for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        self.0.instance()
    }

    fn synthesize_sub(
        &self,
        _config: &Self::Config,
        _challenges: &Challenges<Value<F>>,
        _layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        panic!("use PiCircuit for embedding instead");
    }
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> Circuit<F>
    for PiTestCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    type Config = (PiCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let block_table = BlockTable::construct(meta);
        let tx_table = TxTable::construct(meta);
        (
            PiCircuitConfig::new(
                meta,
                PiCircuitConfigArgs {
                    max_txs: MAX_TXS,
                    max_calldata: MAX_CALLDATA,
                    block_table,
                    tx_table,
                },
            ),
            Challenges::construct(meta),
        )
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        self.0.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

fn run<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
    k: u32,
    public_data: PublicData,
) -> Result<(), Vec<VerifyFailure>> {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let randomness = F::random(&mut rng);
    let rand_rpi = F::random(&mut rng);
    let mut public_data = public_data;
    public_data.chain_id = *MOCK_CHAIN_ID;

    let circuit = PiTestCircuit::<F, MAX_TXS, MAX_CALLDATA>(PiCircuit::new(
        MAX_TXS,
        MAX_CALLDATA,
        randomness,
        rand_rpi,
        public_data,
    ));
    let public_inputs = circuit.0.instance();

    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    prover.verify()
}

#[test]
fn test_default_pi() {
    const MAX_TXS: usize = 2;
    const MAX_CALLDATA: usize = 8;
    let public_data = PublicData::default();

    let k = 17;
    assert_eq!(run::<Fr, MAX_TXS, MAX_CALLDATA>(k, public_data), Ok(()));
}

#[test]
fn test_simple_pi() {
    const MAX_TXS: usize = 8;
    const MAX_CALLDATA: usize = 200;

    let mut public_data = PublicData::default();

    let n_tx = 4;
    for i in 0..n_tx {
        public_data
            .transactions
            .push(CORRECT_MOCK_TXS[i].clone().into());
    }

    let k = 17;
    assert_eq!(run::<Fr, MAX_TXS, MAX_CALLDATA>(k, public_data), Ok(()));
}

fn run_size_check<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
    public_data: [PublicData; 2],
) {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let randomness = F::random(&mut rng);
    let rand_rpi = F::random(&mut rng);

    let circuit = PiTestCircuit::<F, MAX_TXS, MAX_CALLDATA>(PiCircuit::new(
        MAX_TXS,
        MAX_CALLDATA,
        randomness,
        rand_rpi,
        public_data[0].clone(),
    ));
    let public_inputs = circuit.0.instance();
    let prover1 = MockProver::run(20, &circuit, public_inputs).unwrap();

    let circuit2 = PiTestCircuit::<F, MAX_TXS, MAX_CALLDATA>(PiCircuit::new(
        MAX_TXS,
        MAX_CALLDATA,
        randomness,
        rand_rpi,
        public_data[1].clone(),
    ));
    let public_inputs = circuit2.0.instance();
    let prover2 = MockProver::run(20, &circuit, public_inputs).unwrap();

    assert_eq!(prover1.fixed(), prover2.fixed());
    assert_eq!(prover1.permutation(), prover2.permutation());
}

#[test]
fn variadic_size_check() {
    const MAX_TXS: usize = 8;
    const MAX_CALLDATA: usize = 200;

    let mut pub_dat_1 = PublicData {
        chain_id: *MOCK_CHAIN_ID,
        ..Default::default()
    };

    let n_tx = 2;
    for i in 0..n_tx {
        pub_dat_1
            .transactions
            .push(CORRECT_MOCK_TXS[i].clone().into());
    }

    let mut pub_dat_2 = PublicData {
        chain_id: *MOCK_CHAIN_ID,
        ..Default::default()
    };

    let n_tx = 4;
    for i in 0..n_tx {
        pub_dat_2
            .transactions
            .push(CORRECT_MOCK_TXS[i].clone().into());
    }

    run_size_check::<Fr, MAX_TXS, MAX_CALLDATA>([pub_dat_1, pub_dat_2]);
}
