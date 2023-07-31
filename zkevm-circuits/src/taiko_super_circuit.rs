//! The super circuit for taiko

/// for test purpose
#[cfg(any(feature = "test", test))]
pub mod test;

use crate::{
    anchor_tx_circuit::{AnchorTxCircuit, AnchorTxCircuitConfig, AnchorTxCircuitConfigArgs},
    table::{byte_table::ByteTable, BlockTable, KeccakTable, PiTable, TxTable},
    taiko_pi_circuit::{TaikoPiCircuit, TaikoPiCircuitConfig, TaikoPiCircuitConfigArgs},
    util::{log2_ceil, Challenges, SubCircuit, SubCircuitConfig},
    witness::{block_convert, Block},
};
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, CircuitsParams, ProtocolInstance},
    mock::BlockData,
};
use eth_types::{geth_types::GethData, Field};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error, Expression},
};

use itertools::Itertools;
use snark_verifier_sdk::CircuitExt;

/// Configuration of the Super Circuit
#[derive(Clone)]
pub struct SuperCircuitConfig<F: Field> {
    tx_table: TxTable,
    pi_table: PiTable,
    keccak_table: KeccakTable,
    block_table: BlockTable,
    byte_table: ByteTable,
    pi_circuit: TaikoPiCircuitConfig<F>,
    anchor_tx_circuit: AnchorTxCircuitConfig<F>,
}

/// Circuit configuration arguments
pub struct SuperCircuitConfigArgs<F: Field> {
    /// Challenges expressions
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for SuperCircuitConfig<F> {
    type ConfigArgs = SuperCircuitConfigArgs<F>;

    /// Configure SuperCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs { challenges }: Self::ConfigArgs,
    ) -> Self {
        let tx_table = TxTable::construct(meta);
        let pi_table = PiTable::construct(meta);
        let block_table = BlockTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let byte_table = ByteTable::construct(meta);

        let pi_circuit = TaikoPiCircuitConfig::new(
            meta,
            TaikoPiCircuitConfigArgs {
                block_table: block_table.clone(),
                keccak_table: keccak_table.clone(),
                byte_table: byte_table.clone(),
                challenges: challenges.clone(),
            },
        );

        let anchor_tx_circuit = AnchorTxCircuitConfig::new(
            meta,
            AnchorTxCircuitConfigArgs {
                tx_table: tx_table.clone(),
                pi_table: pi_table.clone(),
                byte_table: byte_table.clone(),
                challenges,
            },
        );

        Self {
            tx_table,
            pi_table,
            pi_circuit,
            block_table,
            keccak_table,
            byte_table,
            anchor_tx_circuit,
        }
    }
}

/// The Super Circuit contains all the zkEVM circuits
#[derive(Clone, Default, Debug)]
pub struct SuperCircuit<F: Field> {
    /// Public Input Circuit
    pub pi_circuit: TaikoPiCircuit<F>,
    /// Anchor Transaction Circuit
    pub anchor_tx_circuit: AnchorTxCircuit<F>,
    /// Block witness
    pub block: Block<F>,
}

impl<F: Field> CircuitExt<F> for SuperCircuit<F> {
    fn num_instance(&self) -> Vec<usize> {
        self.instance().iter().map(|v| v.len()).collect_vec()
    }

    fn instances(&self) -> Vec<Vec<F>> {
        self.instance()
    }
}

// Eventhough the SuperCircuit is not a subcircuit we implement the SubCircuit
// trait for it in order to get the `new_from_block` and `instance` methods that
// allow us to generalize integration tests.
impl<F: Field> SubCircuit<F> for SuperCircuit<F> {
    type Config = SuperCircuitConfig<F>;

    fn unusable_rows() -> usize {
        TaikoPiCircuit::<F>::unusable_rows()
    }

    fn new_from_block(block: &Block<F>) -> Self {
        let pi_circuit = TaikoPiCircuit::new_from_block(block);
        let anchor_tx_circuit = AnchorTxCircuit::new_from_block(block);

        SuperCircuit::<_> {
            pi_circuit,
            anchor_tx_circuit,
            block: block.clone(),
        }
    }

    /// Returns suitable inputs for the SuperCircuit.
    fn instance(&self) -> Vec<Vec<F>> {
        let mut instance = Vec::new();
        instance.extend_from_slice(&self.pi_circuit.instance());
        instance
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &Block<F>) -> (usize, usize) {
        [
            TaikoPiCircuit::min_num_rows_block(block),
            AnchorTxCircuit::min_num_rows_block(block),
        ]
        .iter()
        .fold((0, 0), |(x1, y1), (x2, y2)| {
            (std::cmp::max(x1, *x2), std::cmp::max(y1, *y2))
        })
    }

    /// Make the assignments to the SuperCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        self.pi_circuit
            .synthesize_sub(&config.pi_circuit, challenges, layouter)?;
        self.anchor_tx_circuit
            .synthesize_sub(&config.anchor_tx_circuit, challenges, layouter)?;
        Ok(())
    }
}

impl<F: Field> Circuit<F> for SuperCircuit<F> {
    type Config = (SuperCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure_with_params(
        meta: &mut ConstraintSystem<F>,
        _params: Self::Params,
    ) -> Self::Config {
        Self::configure(meta)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);
        (
            SuperCircuitConfig::new(
                meta,
                SuperCircuitConfigArgs {
                    challenges: challenge_exprs,
                },
            ),
            challenges,
        )
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        let randomness = challenges.evm_word();
        config
            .block_table
            .load(&mut layouter, &self.block.context, randomness)?;
        config.keccak_table.dev_load(
            &mut layouter,
            vec![&self.pi_circuit.public_data.rpi_bytes()],
            &challenges,
        )?;
        config.byte_table.load(&mut layouter)?;
        config
            .pi_table
            .load(&mut layouter, &self.block.protocol_instance, &challenges)?;
        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

impl<F: Field> SuperCircuit<F> {
    /// From the witness data, generate a SuperCircuit instance with all of the
    /// sub-circuits filled with their corresponding witnesses.
    ///
    /// Also, return with it the minimum required SRS degree for the
    /// circuit and the Public Inputs needed.
    #[allow(clippy::type_complexity)]
    pub fn build(
        geth_data: GethData,
        circuits_params: CircuitsParams,
        protocol_instance: ProtocolInstance,
    ) -> Result<(u32, Self, Vec<Vec<F>>, CircuitInputBuilder), bus_mapping::Error> {
        let block_data =
            BlockData::new_from_geth_data_with_params(geth_data.clone(), circuits_params);
        let mut builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&geth_data.eth_block, &geth_data.geth_traces)
            .expect("could not handle block tx");

        let ret = Self::build_from_circuit_input_builder(&builder, protocol_instance)?;
        Ok((ret.0, ret.1, ret.2, builder))
    }

    /// From CircuitInputBuilder, generate a SuperCircuit instance with all of
    /// the sub-circuits filled with their corresponding witnesses.
    ///
    /// Also, return with it the minimum required SRS degree for the circuit and
    /// the Public Inputs needed.
    pub fn build_from_circuit_input_builder(
        builder: &CircuitInputBuilder,
        protocol_instance: ProtocolInstance,
    ) -> Result<(u32, Self, Vec<Vec<F>>), bus_mapping::Error> {
        let mut block = block_convert(&builder.block, &builder.code_db).unwrap();
        block.protocol_instance = protocol_instance;
        block.protocol_instance.block_hash = block.eth_block.hash.unwrap();
        block.protocol_instance.parent_hash = block.eth_block.parent_hash;
        let (_, rows_needed) = Self::min_num_rows_block(&block);
        let k = log2_ceil(Self::unusable_rows() + rows_needed);
        log::debug!("super circuit uses k = {}", k);

        let circuit = SuperCircuit::new_from_block(&block);

        let instance = circuit.instance();
        Ok((k, circuit, instance))
    }
}
