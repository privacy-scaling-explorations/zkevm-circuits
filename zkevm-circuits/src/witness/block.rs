use std::collections::HashMap;

use crate::{
    evm_circuit::{detect_fixed_table_tags, util::rlc, EvmCircuit},
    exp_circuit::param::OFFSET_INCREMENT,
    table::{BlockContextFieldTag, PiFieldTag},
    util::{log2_ceil, rlc_be_bytes, SubCircuit},
};
use bus_mapping::{
    circuit_input_builder::{
        self, CircuitsParams, CopyEvent, ExpEvent, ProtocolInstance, ANCHOR_TX_METHOD_SIGNATURE,
    },
    Error,
};
use eth_types::{Address, Field, ToBigEndian, ToLittleEndian, ToScalar, ToWord, Word, H256};
use halo2_proofs::circuit::Value;

use super::{tx::tx_convert, Bytecode, ExecStep, Rw, RwMap, Transaction};

// TODO: Remove fields that are duplicated in`eth_block`
/// Block is the struct used by all circuits, which contains all the needed
/// data for witness generation.
#[derive(Debug, Clone, Default)]
pub struct Block<F> {
    /// The randomness for random linear combination
    pub randomness: F,
    /// Transactions in the block
    pub txs: Vec<Transaction>,
    /// EndBlock step that is repeated after the last transaction and before
    /// reaching the last EVM row.
    pub end_block_not_last: ExecStep,
    /// Last EndBlock step that appears in the last EVM row.
    pub end_block_last: ExecStep,
    /// Read write events in the RwTable
    pub rws: RwMap,
    /// Bytecode used in the block
    pub bytecodes: HashMap<Word, Bytecode>,
    /// The block context
    pub context: BlockContext,
    /// Copy events for the copy circuit's table.
    pub copy_events: Vec<CopyEvent>,
    /// Exponentiation traces for the exponentiation circuit's table.
    pub exp_events: Vec<ExpEvent>,
    /// Pad exponentiation circuit to make selectors fixed.
    pub exp_circuit_pad_to: usize,
    /// Circuit Setup Parameters
    pub circuits_params: CircuitsParams,
    /// Inputs to the SHA3 opcode
    pub sha3_inputs: Vec<Vec<u8>>,
    /// State root of the previous block
    pub prev_state_root: Word, // TODO: Make this H256
    /// Keccak inputs
    pub keccak_inputs: Vec<Vec<u8>>,
    /// Original Block from geth
    pub eth_block: eth_types::Block<eth_types::Transaction>,
    /// Protocol Instance
    pub protocol_instance: Option<ProtocolInstance>,
}

/// Assignments for pi table
pub fn protocol_instance_table_assignments<F: Field>(
    protocol_instance: &ProtocolInstance,
    randomness: Value<F>,
) -> [[Value<F>; 2]; 6] {
    [
        [
            Value::known(F::from(PiFieldTag::Null as u64)),
            Value::known(F::ZERO),
        ],
        [
            Value::known(F::from(PiFieldTag::MethodSign as u64)),
            Value::known(F::from(ANCHOR_TX_METHOD_SIGNATURE as u64)),
        ],
        [
            Value::known(F::from(PiFieldTag::L1Hash as u64)),
            rlc_be_bytes(
                &protocol_instance.meta_hash.l1_hash.to_fixed_bytes(),
                randomness,
            ),
        ],
        [
            Value::known(F::from(PiFieldTag::L1SignalRoot as u64)),
            rlc_be_bytes(&protocol_instance.signal_root.to_fixed_bytes(), randomness),
        ],
        [
            Value::known(F::from(PiFieldTag::L1Height as u64)),
            rlc_be_bytes(
                &protocol_instance
                    .meta_hash
                    .l1_height
                    .to_word()
                    .to_be_bytes(),
                randomness,
            ),
        ],
        [
            Value::known(F::from(PiFieldTag::ParentGasUsed as u64)),
            rlc_be_bytes(
                &(protocol_instance.parent_gas_used as u64)
                    .to_word()
                    .to_be_bytes(),
                randomness,
            ),
        ],
    ]
}

impl<F: Field> Block<F> {
    /// Get a read-write record
    pub(crate) fn get_rws(&self, step: &ExecStep, index: usize) -> Rw {
        self.rws[step.rw_index(index)]
    }

    /// Set protocol instance means in taiko context
    pub fn is_taiko(&self) -> bool {
        self.protocol_instance.is_some()
    }

    /// Obtains the expected Circuit degree needed in order to be able to test
    /// the EvmCircuit with this block without needing to configure the
    /// `ConstraintSystem`.
    pub fn get_test_degree(&self) -> u32 {
        let num_rows_required_for_execution_steps: usize =
            EvmCircuit::<F>::get_num_rows_required(self);
        let num_rows_required_for_rw_table: usize = self.circuits_params.max_rws;
        let num_rows_required_for_fixed_table: usize = detect_fixed_table_tags(self)
            .iter()
            .map(|tag| tag.build::<F>().count())
            .sum();
        let num_rows_required_for_bytecode_table: usize = self
            .bytecodes
            .values()
            .map(|bytecode| bytecode.bytes.len() + 1)
            .sum();
        let num_rows_required_for_copy_table: usize =
            self.copy_events.iter().map(|c| c.bytes.len() * 2).sum();
        let num_rows_required_for_keccak_table: usize = self.keccak_inputs.len();
        let num_rows_required_for_tx_table: usize =
            self.txs.iter().map(|tx| 9 + tx.call_data.len()).sum();
        let num_rows_required_for_exp_table: usize = self
            .exp_events
            .iter()
            .map(|e| e.steps.len() * OFFSET_INCREMENT)
            .sum();

        let rows_needed: usize = itertools::max([
            num_rows_required_for_execution_steps,
            num_rows_required_for_rw_table,
            num_rows_required_for_fixed_table,
            num_rows_required_for_bytecode_table,
            num_rows_required_for_copy_table,
            num_rows_required_for_keccak_table,
            num_rows_required_for_tx_table,
            num_rows_required_for_exp_table,
        ])
        .unwrap();

        let k = log2_ceil(EvmCircuit::<F>::unusable_rows() + rows_needed);
        log::debug!(
            "num_rows_requred_for rw_table={}, fixed_table={}, bytecode_table={}, \
            copy_table={}, keccak_table={}, tx_table={}, exp_table={}",
            num_rows_required_for_rw_table,
            num_rows_required_for_fixed_table,
            num_rows_required_for_bytecode_table,
            num_rows_required_for_copy_table,
            num_rows_required_for_keccak_table,
            num_rows_required_for_tx_table,
            num_rows_required_for_exp_table
        );
        log::debug!("evm circuit uses k = {}, rows = {}", k, rows_needed);
        k
    }
}

/// Block context for execution
#[derive(Debug, Default, Clone)]
pub struct BlockContext {
    /// The address of the miner for the block
    pub coinbase: Address,
    /// The address of the treasury for the base fee
    pub treasury: Option<Address>,
    /// The gas limit of the block
    pub gas_limit: u64,
    /// The number of the block
    pub number: Word,
    /// The timestamp of the block
    pub timestamp: Word,
    /// The difficulty of the blcok
    pub difficulty: Word,
    /// The mix hash of the block
    pub mix_hash: Option<H256>,
    /// The base fee, the minimum amount of gas fee for a transaction
    pub base_fee: Word,
    /// The hash of previous blocks
    pub history_hashes: Vec<Word>,
    /// The chain id
    pub chain_id: Word,
    /// The block hash
    pub block_hash: Word,
}

impl BlockContext {
    /// Assignments for block table
    pub fn table_assignments<F: Field>(&self, randomness: Value<F>) -> Vec<[Value<F>; 3]> {
        [
            vec![
                [
                    Value::known(F::from(BlockContextFieldTag::Coinbase as u64)),
                    Value::known(F::ZERO),
                    Value::known(self.coinbase.to_scalar().unwrap()),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::Treasury as u64)),
                    Value::known(F::ZERO),
                    Value::known(self.treasury.unwrap_or_default().to_scalar().unwrap()),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::Timestamp as u64)),
                    Value::known(F::ZERO),
                    Value::known(self.timestamp.to_scalar().unwrap()),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::Number as u64)),
                    Value::known(F::ZERO),
                    Value::known(self.number.to_scalar().unwrap()),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::Difficulty as u64)),
                    Value::known(F::ZERO),
                    {
                        let difficulty = if self.difficulty.is_zero() {
                            self.mix_hash.unwrap_or_default().to_fixed_bytes()
                        } else {
                            self.difficulty.to_le_bytes()
                        };
                        randomness.map(|randomness| rlc::value(&difficulty, randomness))
                    },
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::GasLimit as u64)),
                    Value::known(F::ZERO),
                    Value::known(F::from(self.gas_limit)),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::BaseFee as u64)),
                    Value::known(F::ZERO),
                    randomness
                        .map(|randomness| rlc::value(&self.base_fee.to_le_bytes(), randomness)),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::ChainId as u64)),
                    Value::known(F::ZERO),
                    randomness
                        .map(|randomness| rlc::value(&self.chain_id.to_le_bytes(), randomness)),
                ],
                [
                    Value::known(F::from(BlockContextFieldTag::BlockHash as u64)),
                    Value::known(self.number.to_scalar().unwrap()),
                    randomness
                        .map(|randomness| rlc::value(&self.block_hash.to_le_bytes(), randomness)),
                ],
            ],
            {
                let len_history = self.history_hashes.len();
                self.history_hashes
                    .iter()
                    .enumerate()
                    .map(|(idx, hash)| {
                        [
                            Value::known(F::from(BlockContextFieldTag::BlockHash as u64)),
                            Value::known((self.number - len_history + idx).to_scalar().unwrap()),
                            randomness
                                .map(|randomness| rlc::value(&hash.to_le_bytes(), randomness)),
                        ]
                    })
                    .collect()
            },
        ]
        .concat()
    }
}

impl From<&circuit_input_builder::Block> for BlockContext {
    fn from(block: &circuit_input_builder::Block) -> Self {
        Self {
            coinbase: block.coinbase,
            treasury: block
                .protocol_instance
                .as_ref()
                .map(|pi| pi.meta_hash.treasury),
            gas_limit: block.gas_limit,
            number: block.number,
            timestamp: block.timestamp,
            difficulty: block.difficulty,
            mix_hash: block.eth_block.mix_hash,
            base_fee: block.base_fee,
            history_hashes: block.history_hashes.clone(),
            chain_id: block.chain_id,
            block_hash: block
                .eth_block
                .hash
                .map(|hash| hash.to_word())
                .unwrap_or_default(),
        }
    }
}

/// Convert a block struct in bus-mapping to a witness block used in circuits
pub fn block_convert<F: Field>(
    block: &circuit_input_builder::Block,
    code_db: &bus_mapping::state_db::CodeDB,
) -> Result<Block<F>, Error> {
    let rws = RwMap::from(&block.container);
    rws.check_value();
    Ok(Block {
        // randomness: F::from(0x100), // Special value to reveal elements after RLC
        randomness: F::from(0xcafeu64),
        context: block.into(),
        rws,
        txs: block
            .txs()
            .iter()
            .enumerate()
            .map(|(idx, tx)| tx_convert(tx, block.chain_id.as_u64(), idx + 1))
            .collect(),
        end_block_not_last: block.block_steps.end_block_not_last.clone(),
        end_block_last: block.block_steps.end_block_last.clone(),
        bytecodes: code_db
            .0
            .values()
            .map(|v| {
                let bytecode = Bytecode::new(v.clone());
                (bytecode.hash, bytecode)
            })
            .collect(),
        copy_events: block.copy_events.clone(),
        exp_events: block.exp_events.clone(),
        sha3_inputs: block.sha3_inputs.clone(),
        circuits_params: block.circuits_params,
        exp_circuit_pad_to: <usize>::default(),
        prev_state_root: block.prev_state_root,
        // Use EVM Circuit's related inputs for keccak inputs
        // Otherwise, it will fail due to tx.v in keccak_inputs_tx_circuit
        // keccak_inputs: circuit_input_builder::keccak_inputs(block, code_db)?,
        keccak_inputs: block.sha3_inputs.clone(),
        eth_block: block.eth_block.clone(),
        protocol_instance: block.protocol_instance.clone(),
    })
}
