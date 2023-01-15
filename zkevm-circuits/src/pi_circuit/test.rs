pub use super::*;
use halo2_proofs::{
    dev::{MockProver, VerifyFailure},
    plonk::Circuit,
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

// We define the PiTestCircuit as a wrapper over PiCircuit extended to take the
// generic const parameters MAX_TXS and MAX_CALLDATA.  This is necessary because
// the trait Circuit requires an implementation of `configure` that doesn't take
// any circuit parameters, and the PiCircuit defines gates that use rotations
// that depend on MAX_TXS and MAX_CALLDATA, so these two values are required
// during the configuration.
/// Test Circuit for PiCircuit
#[cfg(any(feature = "test", test))]
#[derive(Default)]
pub struct PiTestCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
    pub PiCircuit<F>,
);

#[cfg(any(feature = "test", test))]
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
    use halo2_proofs::halo2curves::bn256::Fr;

    const MAX_TXS: usize = 2;
    const MAX_CALLDATA: usize = 8;
    let public_data = PublicData::default();

    let k = 17;
    assert_eq!(run::<Fr, MAX_TXS, MAX_CALLDATA>(k, public_data), Ok(()));
}

#[test]
fn test_simple_pi() {
    use crate::test_util::rand_tx;
    use halo2_proofs::halo2curves::bn256::Fr;

    const MAX_TXS: usize = 8;
    const MAX_CALLDATA: usize = 200;

    let mut rng = ChaCha20Rng::seed_from_u64(2);

    let mut public_data = PublicData::default();
    let chain_id = 1337u64;
    public_data.chain_id = Word::from(chain_id);

    let n_tx = 4;
    for i in 0..n_tx {
        let eth_tx = eth_types::Transaction::from(&rand_tx(&mut rng, chain_id, i & 2 == 0));
        public_data.transactions.push(eth_tx);
    }

    let k = 17;
    assert_eq!(run::<Fr, MAX_TXS, MAX_CALLDATA>(k, public_data), Ok(()));
}
