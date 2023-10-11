use super::{PiCircuit, PiCircuitConfig, PiCircuitConfigArgs};

use eth_types::{self, Field};

use crate::{
    table::{BlockTable, KeccakTable, TxTable, WdTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

/// Public Input Circuit configuration parameters
#[derive(Default)]
pub struct PiCircuitParams {
    /// Max Txs
    pub max_txs: usize,
    /// Max withdrawals
    pub max_withdrawals: usize,
    /// Max Calldata
    pub max_calldata: usize,
}

impl<F: Field> Circuit<F> for PiCircuit<F> {
    type Config = (PiCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = PiCircuitParams;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn params(&self) -> Self::Params {
        PiCircuitParams {
            max_txs: self.max_txs,
            max_withdrawals: self.max_withdrawals,
            max_calldata: self.max_calldata,
        }
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let block_table = BlockTable::construct(meta);
        let tx_table = TxTable::construct(meta);
        let wd_table = WdTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);
        (
            PiCircuitConfig::new(
                meta,
                PiCircuitConfigArgs {
                    max_txs: params.max_txs,
                    max_withdrawals: params.max_withdrawals,
                    max_calldata: params.max_calldata,
                    block_table,
                    tx_table,
                    wd_table,
                    keccak_table,
                    challenges: challenge_exprs,
                },
            ),
            challenges,
        )
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!();
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        // assign keccak table
        let rpi_bytes = self.public_data.get_pi_bytes(
            config.max_txs,
            config.max_withdrawals,
            config.max_calldata,
        );
        config
            .keccak_table
            .dev_load(&mut layouter, vec![&rpi_bytes], &challenges)?;

        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}
