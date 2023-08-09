pub use super::TxCircuit;

use crate::{
    table::{KeccakTable, TxTable},
    tx_circuit::{TxCircuitConfig, TxCircuitConfigArgs},
    util::{Challenges, SubCircuit, SubCircuitConfig},
};
use bus_mapping::circuit_input_builder::keccak_inputs_tx_circuit;
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};
use log::error;

impl<F: Field> Circuit<F> for TxCircuit<F> {
    type Config = (TxCircuitConfig<F>, Challenges, KeccakTable);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = TxTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            TxCircuitConfig::new(
                meta,
                TxCircuitConfigArgs {
                    tx_table,
                    keccak_table: keccak_table.clone(),
                    challenges,
                },
            )
        };

        (config, challenges, keccak_table)
    }

    fn synthesize(
        &self,
        (config, challenges, keccak_table): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);

        keccak_table.dev_load(
            &mut layouter,
            &keccak_inputs_tx_circuit(&self.txs[..], self.chain_id).map_err(|e| {
                error!("keccak_inputs_tx_circuit error: {:?}", e);
                Error::Synthesis
            })?,
            &challenges,
        )?;
        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}
