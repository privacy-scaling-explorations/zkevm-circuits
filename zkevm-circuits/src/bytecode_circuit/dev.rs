pub use super::circuit::BytecodeCircuit;

use crate::{
    bytecode_circuit::circuit::{BytecodeCircuitConfig, BytecodeCircuitConfigArgs},
    table::{BytecodeTable, KeccakTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

impl<F: Field> Circuit<F> for BytecodeCircuit<F> {
    type Config = (BytecodeCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let bytecode_table = BytecodeTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            BytecodeCircuitConfig::new(
                meta,
                BytecodeCircuitConfigArgs {
                    bytecode_table,
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

        config
            .keccak_table
            .dev_load(&mut layouter, &self.bytecodes.iter(), &challenges)?;
        self.synthesize_sub(&config, &challenges, &mut layouter)?;
        Ok(())
    }
}
