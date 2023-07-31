pub use super::AnchorTxCircuit;
use crate::{
    anchor_tx_circuit::{AnchorTxCircuitConfig, AnchorTxCircuitConfigArgs},
    table::{byte_table::ByteTable, PiTable, TxTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use bus_mapping::circuit_input_builder::ProtocolInstance;
use eth_types::{Field, H256};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

/// Test circuit for the anchor tx circuit.
#[derive(Clone, Debug, Default)]
pub struct TestAnchorTxCircuit<F: Field> {
    protocol_instance: ProtocolInstance,
    circuit: AnchorTxCircuit<F>,
}

impl<F: Field> TestAnchorTxCircuit<F> {
    /// Create a new test circuit from a block.
    pub fn new_from_block(block: &witness::Block<F>) -> Self {
        TestAnchorTxCircuit {
            protocol_instance: block.protocol_instance.clone(),
            circuit: AnchorTxCircuit::new_from_block(block),
        }
    }

    /// Modify the sign hash for test
    pub fn sign_hash(&mut self, hash: H256) {
        self.circuit.anchor_tx.tx_sign_hash = Some(hash);
        self.circuit.txs[0].tx_sign_hash = Some(hash);
    }
}

impl<F: Field> Circuit<F> for TestAnchorTxCircuit<F> {
    type Config = (AnchorTxCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = TxTable::construct(meta);
        let pi_table = PiTable::construct(meta);
        let byte_table = ByteTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            AnchorTxCircuitConfig::new(
                meta,
                AnchorTxCircuitConfigArgs {
                    tx_table,
                    pi_table,
                    byte_table,
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
        config
            .pi_table
            .load(&mut layouter, &self.protocol_instance, &challenges)?;
        config.byte_table.load(&mut layouter)?;
        self.circuit
            .synthesize_sub(&config, &challenges, &mut layouter)
    }
}
