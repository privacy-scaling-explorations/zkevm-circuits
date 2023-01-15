pub use super::keccak_packed_multi::*;
use crate::table::KeccakTable;
use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};

use log::error;

impl<F: Field> Circuit<F> for KeccakCircuit<F> {
    type Config = (KeccakCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            KeccakCircuitConfig::new(
                meta,
                KeccakCircuitConfigArgs {
                    keccak_table,
                    challenges,
                },
            )
        };
        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

fn verify<F: Field>(k: u32, inputs: Vec<Vec<u8>>, success: bool) {
    let circuit = KeccakCircuit::new(Some(2usize.pow(k)), inputs);

    let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
    let verify_result = prover.verify();
    if verify_result.is_ok() != success {
        if let Some(errors) = verify_result.err() {
            for error in errors.iter() {
                error!("{}", error);
            }
        }
        panic!();
    }
}

#[test]
fn packed_multi_keccak_simple() {
    use halo2_proofs::halo2curves::bn256::Fr;

    let k = 11;
    let inputs = vec![
        vec![],
        (0u8..1).collect::<Vec<_>>(),
        (0u8..135).collect::<Vec<_>>(),
        (0u8..136).collect::<Vec<_>>(),
        (0u8..200).collect::<Vec<_>>(),
    ];
    verify::<Fr>(k, inputs, true);
}
