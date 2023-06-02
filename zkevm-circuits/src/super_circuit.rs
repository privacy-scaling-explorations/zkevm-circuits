//! The Super Circuit is a circuit that contains all the circuits of the
//! zkEVM in order to achieve two things:
//! - Check the correct integration between circuits via the shared lookup tables, to verify that
//!   the table layouts match.
//! - Allow having a single circuit setup for which a proof can be generated that would be verified
//!   under a single aggregation circuit for the first milestone.
//!
//! The current implementation contains the following circuits:
//!
//! - [x] EVM Circuit
//! - [ ] State Circuit
//! - [x] Tx Circuit
//! - [x] Bytecode Circuit
//! - [x] Copy Circuit
//! - [x] Exponentiation Circuit
//! - [ ] Keccak Circuit
//! - [ ] MPT Circuit
//! - [x] PublicInputs Circuit
//!
//! And the following shared tables, with the circuits that use them:
//!
//! - [x] Copy Table
//!   - [x] Copy Circuit
//!   - [x] EVM Circuit
//! - [x] Exponentiation Table
//!   - [x] EVM Circuit
//! - [ ] Rw Table
//!   - [ ] State Circuit
//!   - [ ] EVM Circuit
//!   - [ ] Copy Circuit
//! - [x] Tx Table
//!   - [x] Tx Circuit
//!   - [x] EVM Circuit
//!   - [x] Copy Circuit
//!   - [x] PublicInputs Circuit
//! - [x] Bytecode Table
//!   - [x] Bytecode Circuit
//!   - [x] EVM Circuit
//!   - [x] Copy Circuit
//! - [ ] Block Table
//!   - [ ] EVM Circuit
//!   - [x] PublicInputs Circuit
//! - [ ] MPT Table
//!   - [ ] MPT Circuit
//!   - [ ] State Circuit
//! - [x] Keccak Table
//!   - [ ] Keccak Circuit
//!   - [ ] EVM Circuit
//!   - [x] Bytecode Circuit
//!   - [x] Tx Circuit
//!   - [ ] MPT Circuit

#[cfg(any(feature = "test", test))]
pub(crate) mod test;

use crate::{
    bytecode_circuit::circuit::{
        BytecodeCircuit, BytecodeCircuitConfig, BytecodeCircuitConfigArgs,
    },
    copy_circuit::{CopyCircuit, CopyCircuitConfig, CopyCircuitConfigArgs},
    evm_circuit::{EvmCircuit, EvmCircuitConfig, EvmCircuitConfigArgs},
    exp_circuit::{ExpCircuit, ExpCircuitConfig},
    keccak_circuit::{KeccakCircuit, KeccakCircuitConfig, KeccakCircuitConfigArgs},
    pi_circuit::{PiCircuit, PiCircuitConfig, PiCircuitConfigArgs},
    state_circuit::{StateCircuit, StateCircuitConfig, StateCircuitConfigArgs},
    table::{
        BlockTable, BytecodeTable, CopyTable, ExpTable, KeccakTable, MptTable, RwTable, TxTable,
    },
    tx_circuit::{TxCircuit, TxCircuitConfig, TxCircuitConfigArgs},
    util::{log2_ceil, Challenges, SubCircuit, SubCircuitConfig},
    witness::{block_convert, Block, MptUpdates},
};
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, ConcreteCP},
    mock::BlockData,
};
use eth_types::{geth_types::GethData, Field};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error, Expression},
};

use std::array;

/// Configuration of the Super Circuit
#[derive(Clone)]
pub struct SuperCircuitConfig<F: Field> {
    block_table: BlockTable,
    mpt_table: MptTable,
    evm_circuit: EvmCircuitConfig<F>,
    state_circuit: StateCircuitConfig<F>,
    tx_circuit: TxCircuitConfig<F>,
    bytecode_circuit: BytecodeCircuitConfig<F>,
    copy_circuit: CopyCircuitConfig<F>,
    keccak_circuit: KeccakCircuitConfig<F>,
    pi_circuit: PiCircuitConfig<F>,
    exp_circuit: ExpCircuitConfig<F>,
}

/// Circuit configuration arguments
pub struct SuperCircuitConfigArgs<F: Field> {
    /// Max txs
    pub max_txs: usize,
    /// Max calldata
    pub max_calldata: usize,
    /// Mock randomness
    pub mock_randomness: F,
}

impl<F: Field> SubCircuitConfig<F> for SuperCircuitConfig<F> {
    type ConfigArgs = SuperCircuitConfigArgs<F>;

    /// Configure SuperCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            max_txs,
            max_calldata,
            mock_randomness,
        }: Self::ConfigArgs,
    ) -> Self {
        let tx_table = TxTable::construct(meta);
        let rw_table = RwTable::construct(meta);
        let mpt_table = MptTable::construct(meta);
        let bytecode_table = BytecodeTable::construct(meta);
        let block_table = BlockTable::construct(meta);
        let q_copy_table = meta.fixed_column();
        let copy_table = CopyTable::construct(meta, q_copy_table);
        let exp_table = ExpTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);

        // Use a mock randomness instead of the randomness derived from the challange
        // (either from mock or real prover) to help debugging assignments.
        let power_of_randomness: [Expression<F>; 31] =
            array::from_fn(|i| Expression::Constant(mock_randomness.pow([1 + i as u64, 0, 0, 0])));

        let challenges = Challenges::mock(
            power_of_randomness[0].clone(),
            power_of_randomness[0].clone(),
            power_of_randomness[0].clone(),
        );

        let keccak_circuit = KeccakCircuitConfig::new(
            meta,
            KeccakCircuitConfigArgs {
                keccak_table: keccak_table.clone(),
                challenges: challenges.clone(),
            },
        );

        let pi_circuit = PiCircuitConfig::new(
            meta,
            PiCircuitConfigArgs {
                max_txs,
                max_calldata,
                block_table: block_table.clone(),
                tx_table: tx_table.clone(),
            },
        );
        let tx_circuit = TxCircuitConfig::new(
            meta,
            TxCircuitConfigArgs {
                tx_table: tx_table.clone(),
                keccak_table: keccak_table.clone(),
                challenges: challenges.clone(),
            },
        );
        let bytecode_circuit = BytecodeCircuitConfig::new(
            meta,
            BytecodeCircuitConfigArgs {
                bytecode_table: bytecode_table.clone(),
                keccak_table: keccak_table.clone(),
                challenges: challenges.clone(),
            },
        );
        let copy_circuit = CopyCircuitConfig::new(
            meta,
            CopyCircuitConfigArgs {
                tx_table: tx_table.clone(),
                rw_table,
                bytecode_table: bytecode_table.clone(),
                copy_table,
                q_enable: q_copy_table,
                challenges: challenges.clone(),
            },
        );
        let state_circuit = StateCircuitConfig::new(
            meta,
            StateCircuitConfigArgs {
                rw_table,
                mpt_table,
                challenges: challenges.clone(),
            },
        );
        let exp_circuit = ExpCircuitConfig::new(meta, exp_table);
        let evm_circuit = EvmCircuitConfig::new(
            meta,
            EvmCircuitConfigArgs {
                challenges,
                tx_table,
                rw_table,
                bytecode_table,
                block_table: block_table.clone(),
                copy_table,
                keccak_table,
                exp_table,
            },
        );

        Self {
            block_table,
            mpt_table,
            evm_circuit,
            state_circuit,
            copy_circuit,
            tx_circuit,
            bytecode_circuit,
            keccak_circuit,
            pi_circuit,
            exp_circuit,
        }
    }
}

/// The Super Circuit contains all the zkEVM circuits
#[derive(Clone, Default, Debug)]
pub struct SuperCircuit<F: Field> {
    /// EVM Circuit
    pub evm_circuit: EvmCircuit<F>,
    /// State Circuit
    pub state_circuit: StateCircuit<F>,
    /// The transaction circuit that will be used in the `synthesize` step.
    pub tx_circuit: TxCircuit<F>,
    /// Public Input Circuit
    pub pi_circuit: PiCircuit<F>,
    /// Bytecode Circuit
    pub bytecode_circuit: BytecodeCircuit<F>,
    /// Copy Circuit
    pub copy_circuit: CopyCircuit<F>,
    /// Exp Circuit
    pub exp_circuit: ExpCircuit<F>,
    /// Keccak Circuit
    pub keccak_circuit: KeccakCircuit<F>,
    /// Circuits Parameters
    pub circuits_params: ConcreteCP,
    /// Mock randomness
    pub mock_randomness: F,
}

impl<F: Field> SuperCircuit<F> {
    /// Return the number of rows required to verify a given block
    pub fn get_num_rows_required(block: &Block<F>) -> usize {
        let num_rows_evm_circuit = EvmCircuit::<F>::get_num_rows_required(block);
        let num_rows_tx_circuit =
            TxCircuitConfig::<F>::get_num_rows_required(block.circuits_params.max_txs);
        num_rows_evm_circuit.max(num_rows_tx_circuit)
    }
}

// Eventhough the SuperCircuit is not a subcircuit we implement the SubCircuit
// trait for it in order to get the `new_from_block` and `instance` methods that
// allow us to generalize integration tests.
impl<F: Field> SubCircuit<F> for SuperCircuit<F> {
    type Config = SuperCircuitConfig<F>;

    fn unusable_rows() -> usize {
        itertools::max([
            EvmCircuit::<F>::unusable_rows(),
            StateCircuit::<F>::unusable_rows(),
            TxCircuit::<F>::unusable_rows(),
            PiCircuit::<F>::unusable_rows(),
            BytecodeCircuit::<F>::unusable_rows(),
            CopyCircuit::<F>::unusable_rows(),
            ExpCircuit::<F>::unusable_rows(),
            KeccakCircuit::<F>::unusable_rows(),
        ])
        .unwrap()
    }

    fn new_from_block(block: &Block<F>) -> Self {
        let evm_circuit = EvmCircuit::new_from_block(block);
        let state_circuit = StateCircuit::new_from_block(block);
        let tx_circuit = TxCircuit::new_from_block(block);
        let pi_circuit = PiCircuit::new_from_block(block);
        let bytecode_circuit = BytecodeCircuit::new_from_block(block);
        let copy_circuit = CopyCircuit::new_from_block_no_external(block);
        let exp_circuit = ExpCircuit::new_from_block(block);
        let keccak_circuit = KeccakCircuit::new_from_block(block);

        SuperCircuit::<_> {
            evm_circuit,
            state_circuit,
            tx_circuit,
            pi_circuit,
            bytecode_circuit,
            copy_circuit,
            exp_circuit,
            keccak_circuit,
            circuits_params: block.circuits_params,
            mock_randomness: block.randomness,
        }
    }

    /// Returns suitable inputs for the SuperCircuit.
    fn instance(&self) -> Vec<Vec<F>> {
        let mut instance = Vec::new();
        instance.extend_from_slice(&self.keccak_circuit.instance());
        instance.extend_from_slice(&self.pi_circuit.instance());
        instance.extend_from_slice(&self.tx_circuit.instance());
        instance.extend_from_slice(&self.bytecode_circuit.instance());
        instance.extend_from_slice(&self.copy_circuit.instance());
        instance.extend_from_slice(&self.state_circuit.instance());
        instance.extend_from_slice(&self.exp_circuit.instance());
        instance.extend_from_slice(&self.evm_circuit.instance());

        instance
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &Block<F>) -> (usize, usize) {
        let evm = EvmCircuit::min_num_rows_block(block);
        let state = StateCircuit::min_num_rows_block(block);
        let bytecode = BytecodeCircuit::min_num_rows_block(block);
        let copy = CopyCircuit::min_num_rows_block(block);
        let keccak = KeccakCircuit::min_num_rows_block(block);
        let tx = TxCircuit::min_num_rows_block(block);
        let exp = ExpCircuit::min_num_rows_block(block);
        let pi = PiCircuit::min_num_rows_block(block);

        let rows: Vec<(usize, usize)> = vec![evm, state, bytecode, copy, keccak, tx, exp, pi];
        let (rows_without_padding, rows_with_padding): (Vec<usize>, Vec<usize>) =
            rows.into_iter().unzip();
        (
            itertools::max(rows_without_padding).unwrap(),
            itertools::max(rows_with_padding).unwrap(),
        )
    }

    /// Make the assignments to the SuperCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        self.keccak_circuit
            .synthesize_sub(&config.keccak_circuit, challenges, layouter)?;
        self.bytecode_circuit
            .synthesize_sub(&config.bytecode_circuit, challenges, layouter)?;
        self.tx_circuit
            .synthesize_sub(&config.tx_circuit, challenges, layouter)?;
        self.state_circuit
            .synthesize_sub(&config.state_circuit, challenges, layouter)?;
        self.copy_circuit
            .synthesize_sub(&config.copy_circuit, challenges, layouter)?;
        self.exp_circuit
            .synthesize_sub(&config.exp_circuit, challenges, layouter)?;
        self.evm_circuit
            .synthesize_sub(&config.evm_circuit, challenges, layouter)?;
        self.pi_circuit
            .synthesize_sub(&config.pi_circuit, challenges, layouter)?;
        Ok(())
    }
}

/// Super Circuit configuration parameters
#[derive(Default)]
pub struct SuperCircuitParams<F: Field> {
    max_txs: usize,
    max_calldata: usize,
    mock_randomness: F,
}

impl<F: Field> Circuit<F> for SuperCircuit<F> {
    type Config = SuperCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = SuperCircuitParams<F>;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn params(&self) -> Self::Params {
        SuperCircuitParams {
            max_txs: self.circuits_params.max_txs,
            max_calldata: self.circuits_params.max_calldata,
            mock_randomness: self.mock_randomness,
        }
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        Self::Config::new(
            meta,
            SuperCircuitConfigArgs {
                max_txs: params.max_txs,
                max_calldata: params.max_calldata,
                mock_randomness: params.mock_randomness,
            },
        )
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!();
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let block = self.evm_circuit.block.as_ref().unwrap();
        let challenges = Challenges::mock(
            Value::known(block.randomness),
            Value::known(block.randomness),
            Value::known(block.randomness),
        );
        let rws = &self.state_circuit.rows;

        config.block_table.load(
            &mut layouter,
            &block.context,
            Value::known(block.randomness),
        )?;

        config.mpt_table.load(
            &mut layouter,
            &MptUpdates::mock_from(rws),
            Value::known(block.randomness),
        )?;

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
        circuits_params: ConcreteCP,
        mock_randomness: F,
    ) -> Result<(u32, Self, Vec<Vec<F>>, CircuitInputBuilder<ConcreteCP>), bus_mapping::Error> {
        let block_data =
            BlockData::new_from_geth_data_with_params(geth_data.clone(), circuits_params);
        let mut builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&geth_data.eth_block, &geth_data.geth_traces)
            .expect("could not handle block tx");

        let ret = Self::build_from_circuit_input_builder(&builder, mock_randomness)?;
        Ok((ret.0, ret.1, ret.2, builder))
    }

    /// From CircuitInputBuilder, generate a SuperCircuit instance with all of
    /// the sub-circuits filled with their corresponding witnesses.
    ///
    /// Also, return with it the minimum required SRS degree for the circuit and
    /// the Public Inputs needed.
    pub fn build_from_circuit_input_builder(
        builder: &CircuitInputBuilder<ConcreteCP>,
        mock_randomness: F,
    ) -> Result<(u32, Self, Vec<Vec<F>>), bus_mapping::Error> {
        let mut block = block_convert(&builder.block, &builder.code_db).unwrap();
        block.randomness = mock_randomness;

        let (_, rows_needed) = Self::min_num_rows_block(&block);
        let k = log2_ceil(Self::unusable_rows() + rows_needed);
        log::debug!("super circuit uses k = {}", k);

        let circuit = SuperCircuit::new_from_block(&block);

        let instance = circuit.instance();
        Ok((k, circuit, instance))
    }
}
