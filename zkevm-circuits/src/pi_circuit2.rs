//! Use the hash value as public input.
//!
//! We will use three lookup tables to implement the circuit.
//! 1. rlp_table: txs -> rlp
//! 2. compress_table: rlp -> compress
//! 3. hash_table: compress -> hash
//!
//! The dataflow:
//! ```
//! +----------+         +-----------+       +------------+
//! |   txs    +---------> compress  +------->   hash     |
//! |          |         |           |       |            |
//! +----------+         +-----------+       +------------+
//! ```

use crate::{
    evm_circuit::util::constraint_builder::BaseConstraintBuilder,
    witness::{Block, BlockContext},
};
use bytes::Bytes;
use eth_types::geth_types::BlockConstants;
use eth_types::sign_types::SignData;
use eth_types::H256;
use eth_types::{
    geth_types::Transaction, Address, BigEndianHash, Field, ToBigEndian, ToLittleEndian, ToScalar,
    Word,
};
use ethers_core::utils::keccak256;
use halo2_proofs::{
    circuit,
    plonk::{Expression, Instance},
};
use itertools::Itertools;
use rlp::RlpStream;
use std::marker::PhantomData;

use crate::table::TxFieldTag;
use crate::table::TxTable;
use crate::table::{BlockTable, KeccakTable};
use crate::util::{random_linear_combine_word as rlc, Challenges, SubCircuit, SubCircuitConfig};
use crate::witness;
use gadgets::is_zero::IsZeroChip;
use gadgets::util::{not, or, Expr};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};

/// Fixed by the spec
const TX_LEN: usize = 10;
const BLOCK_LEN: usize = 7 + 256;
const EXTRA_LEN: usize = 2;
const ZERO_BYTE_GAS_COST: u64 = 4;
const NONZERO_BYTE_GAS_COST: u64 = 16;
const MAX_DEGREE: usize = 10;

/// Values of the block table (as in the spec)
#[derive(Clone, Default, Debug)]
pub struct BlockValues {
    coinbase: Address,
    gas_limit: u64,
    number: u64,
    timestamp: u64,
    difficulty: Word,
    base_fee: Word, // NOTE: BaseFee was added by EIP-1559 and is ignored in legacy headers.
    chain_id: u64,
    history_hashes: Vec<H256>,
}

/// Values of the tx table (as in the spec)
#[derive(Default, Debug, Clone)]
pub struct TxValues {
    nonce: Word,
    gas: Word, //gas limit
    gas_price: Word,
    from_addr: Address,
    to_addr: Address,
    is_create: u64,
    value: Word,
    call_data_len: u64,
    call_data_gas_cost: u64,
    tx_sign_hash: [u8; 32],
}

/// Extra values (not contained in block or tx tables)
#[derive(Default, Debug, Clone)]
pub struct ExtraValues {
    // block_hash: H256,
    state_root: H256,
    prev_state_root: H256,
}

/// PublicData contains all the values that the PiCircuit recieves as input
#[derive(Debug, Clone, Default)]
pub struct PublicData {
    /// chain id
    pub chain_id: Word,
    /// History hashes contains the most recent 256 block hashes in history,
    /// where the latest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// Block Transactions
    pub transactions: Vec<eth_types::Transaction>,
    /// Block State Root
    pub state_root: H256,
    /// Previous block root
    pub prev_state_root: H256,
    /// Constants related to Ethereum block
    pub block_constants: BlockConstants,
    /// Block context
    pub block_ctx: BlockContext,
}

impl PublicData {
    /// Returns struct with values for the block table
    pub fn get_block_table_values(&self) -> BlockValues {
        let history_hashes = [
            vec![H256::zero(); 256 - self.history_hashes.len()],
            self.history_hashes
                .iter()
                .map(|&hash| H256::from(hash.to_be_bytes()))
                .collect(),
        ]
        .concat();
        BlockValues {
            coinbase: self.block_constants.coinbase,
            gas_limit: self.block_constants.gas_limit.as_u64(),
            number: self.block_constants.number.as_u64(),
            timestamp: self.block_constants.timestamp.as_u64(),
            difficulty: self.block_constants.difficulty,
            base_fee: self.block_constants.base_fee,
            chain_id: self.chain_id.as_u64(),
            history_hashes,
        }
    }

    /// Returns struct with values for the tx table
    pub fn get_tx_table_values(&self) -> Vec<TxValues> {
        let chain_id: u64 = self
            .chain_id
            .try_into()
            .expect("Error converting chain_id to u64");
        let mut tx_vals = vec![];
        for tx in &self.txs() {
            let sign_data: SignData = tx
                .sign_data(chain_id)
                .expect("Error computing tx_sign_hash");
            let mut msg_hash_le = [0u8; 32];
            msg_hash_le.copy_from_slice(sign_data.msg_hash.to_bytes().as_slice());
            tx_vals.push(TxValues {
                nonce: tx.nonce,
                gas_price: tx.gas_price,
                gas: tx.gas_limit,
                from_addr: tx.from,
                to_addr: tx.to.unwrap_or_else(Address::zero),
                is_create: (tx.to.is_none() as u64),
                value: tx.value,
                call_data_len: tx.call_data.0.len() as u64,
                call_data_gas_cost: tx.call_data.0.iter().fold(0, |acc, byte| {
                    acc + if *byte == 0 {
                        ZERO_BYTE_GAS_COST
                    } else {
                        NONZERO_BYTE_GAS_COST
                    }
                }),
                tx_sign_hash: msg_hash_le,
            });
        }
        tx_vals
    }

    fn get_block_rlc<F: Field>(&self) -> Value<F> {
        todo!()
    }

    fn get_txs_rlc<F: Field>(&self) -> Value<F> {
        todo!()
    }

    /// Returns struct with the extra values
    pub fn get_extra_values(&self) -> ExtraValues {
        ExtraValues {
            // block_hash: self.hash.unwrap_or_else(H256::zero),
            state_root: self.state_root,
            prev_state_root: self.prev_state_root,
        }
    }

    fn txs(&self) -> Vec<Transaction> {
        self.transactions.iter().map(Transaction::from).collect()
    }

    fn get_block_rlp_and_hash<F: Field>(
        &self,
        txs_hash: H256,
        challenges: &Challenges<Value<F>>,
    ) -> (Bytes, Value<F>, usize, Value<F>) {
        use crate::evm_circuit::util::rlc;
        let mut stream = RlpStream::new();
        stream.begin_unbounded_list();
        stream
            .append(&self.block_constants.coinbase)
            .append(&self.block_constants.gas_limit)
            .append(&self.block_constants.number)
            .append(&self.block_constants.timestamp)
            .append(&self.block_constants.difficulty)
            .append(&self.block_constants.base_fee)
            .append(&self.chain_id)
            .append_list(&self.history_hashes)
            .append(&self.state_root)
            .append(&self.prev_state_root)
            .append(&txs_hash);
        stream.finalize_unbounded_list();

        let rlp: Bytes = stream.out().into();
        let randomness = challenges.evm_word();
        let rlp_rlc = randomness.map(|randomness| rlc::value(rlp.iter(), randomness));
        let len = rlp.len();
        let hash = keccak256(rlp);
        let hash_rlc = randomness.map(|randomness| rlc::value(hash.iter(), randomness));
        (rlp, rlp_rlc, len, hash_rlc)
    }

    fn get_txs_rlp_and_hash<F: Field>(
        &self,
        challenges: &Challenges<Value<F>>,
    ) -> (Bytes, Value<F>, usize, H256, Value<F>) {
        use crate::evm_circuit::util::rlc;
        let mut stream = RlpStream::new_list(self.transactions.len());
        for tx in self.transactions {
            stream.append_raw(&tx.rlp(), 1);
        }
        let rlp: Bytes = stream.out().into();
        let randomness = challenges.evm_word();
        let rlp_rlc = randomness.map(|randomness| rlc::value(rlp.iter(), randomness));
        let len = rlp.len();
        let hash = keccak256(rlp);
        let hash_rlc = randomness.map(|randomness| rlc::value(hash.iter(), randomness));
        (rlp, rlp_rlc, len, hash.into(), hash_rlc)
    }
}

/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct PiCircuitConfig<F: Field> {
    /// Max number of supported transactions
    max_txs: usize,
    /// Max number of supported calldata bytes
    max_calldata: usize,

    // total rpi = block + history hashes + rlc(hash(rlp(txlist))) (keccak output)
    block: Column<Advice>,
    block_rlc_acc: Column<Advice>, // rlp input
    block_rlp_len: Column<Advice>, // rlp result len(keccak len)
    block_rlp: Column<Advice>,     // keccak input
    block_keccak: Column<Advice>,  // keccak
    q_block_start: Selector,
    q_block_not_end: Selector,

    // txlist
    txs: Column<Advice>,
    txs_rlc_acc: Column<Advice>, // rlp input
    txs_rlp_len: Column<Advice>, // rlp result len(keccak len)
    txs_rlp: Column<Advice>,     // keccak input
    txs_keccak: Column<Advice>,  // keccak input
    q_txs_start: Selector,
    q_txs_not_end: Selector,

    pi: Column<Instance>, // keccak_hi, keccak_lo
    // rlp_table
    // rlc(txlist) -> rlc(rlp(txlist))
    q_rlp_table: Selector,
    rlp_table: [Column<Advice>; 4], // [enable, input, len, output]
    // keccak_table
    // rlc(compressed) -> rlc(keccak(compressed)
    q_keccak_table: Selector,
    keccak_table: KeccakTable,

    // External tables
    q_block_table: Selector,
    block_table: BlockTable,

    // tx table
    q_tx_table: Selector,
    tx_table: TxTable, // txlist hash, pi hash
    q_tx_calldata: Selector,
    q_calldata_start: Selector,
    tx_id_inv: Column<Advice>,
    tx_value_inv: Column<Advice>,
    tx_id_diff_inv: Column<Advice>,
    fixed_u16: Column<Fixed>,
    calldata_gas_cost: Column<Advice>,
    is_final: Column<Advice>,

    _marker: PhantomData<F>,
}

/// Circuit configuration arguments
pub struct PiCircuitConfigArgs<F: Field> {
    /// Max number of supported transactions
    pub max_txs: usize,
    /// Max number of supported calldata bytes
    pub max_calldata: usize,
    /// TxTable
    pub tx_table: TxTable,
    /// BlockTable
    pub block_table: BlockTable,
    /// RlpTable
    pub rlp_table: [Column<Advice>; 4],
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

macro_rules! format_str {
        ($($arg:tt)*) => {{
            let res = format!($($arg)*);
            ::std::boxed::Box::leak(res.into_boxed_str())
        }}
}

impl<F: Field> PiCircuitConfig<F> {
    fn constraint(
        meta: &mut ConstraintSystem<F>,
        name: &'static str,
        q_rpi_start: Selector,
        q_rpi_not_end: Selector,
        rpi: Column<Advice>,
        rpi_rlc_acc: Column<Advice>,
        rpi_rlp_len: Column<Advice>,
        rpi_rlp: Column<Advice>,
        rpi_keccak: Column<Advice>,
        q_rlp_table: Selector,
        rlp_table: [Column<Advice>; 4],
        q_keccak_table: Selector,
        keccak_table: KeccakTable,
        challenges: &Challenges<Expression<F>>,
    ) {
        meta.create_gate(
            format_str!("{name}_rlc_acc_next = {name}_rlc_acc * r + {name}_next"),
            |meta| {
                let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
                let q_rpi_not_end = meta.query_selector(q_rpi_not_end);
                let rpi_rlc_acc_next = meta.query_advice(rpi_rlc_acc, Rotation::next());
                let rpi_rlc_acc = meta.query_advice(rpi_rlc_acc, Rotation::cur());
                let rpi_next = meta.query_advice(rpi, Rotation::next());
                let r = challenges.evm_word();

                cb.require_equal("", rpi_rlc_acc_next, rpi_rlc_acc * r + rpi_next);

                cb.gate(q_rpi_not_end)
            },
        );

        meta.create_gate(format_str!("{name}_rlc_acc[0] = {name}[0]"), |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let q_rpi_start = meta.query_selector(q_rpi_start);
            let rpi_rlc_acc = meta.query_advice(rpi_rlc_acc, Rotation::cur());
            let rpi = meta.query_advice(rpi, Rotation::cur());

            cb.require_equal("", rpi_rlc_acc, rpi);

            cb.gate(q_rpi_start)
        });

        meta.create_gate(
            format_str!("{name}_rlc_acc_next = {name}_rlc_acc * r + {name}_next"),
            |meta| {
                let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
                let q_rpi_not_end = meta.query_selector(q_rpi_not_end);
                let rpi_rlc_acc_next = meta.query_advice(rpi_rlc_acc, Rotation::next());
                let rpi_rlc_acc = meta.query_advice(rpi_rlc_acc, Rotation::cur());
                let rpi_next = meta.query_advice(rpi, Rotation::next());
                let r = challenges.evm_word();

                cb.require_equal("", rpi_rlc_acc_next, rpi_rlc_acc * r + rpi_next);

                cb.gate(q_rpi_not_end)
            },
        );

        meta.lookup_any(format_str!("lookup {name} rlp"), |meta| {
            let q_rlp_table = meta.query_selector(q_rlp_table);

            let rpi_rlc_acc = meta.query_advice(rpi_rlc_acc, Rotation::cur());
            let rpi_rlp_len = meta.query_advice(rpi_rlp_len, Rotation::cur());
            let rpi_rlp = meta.query_advice(rpi_rlp, Rotation::cur());
            vec![
                (
                    q_rlp_table.expr() * 1.expr(),
                    meta.query_advice(rlp_table[0], Rotation::cur()),
                ),
                (
                    q_rlp_table.expr() * rpi_rlc_acc,
                    meta.query_advice(rlp_table[1], Rotation::cur()),
                ),
                (
                    q_rlp_table.expr() * rpi_rlp_len,
                    meta.query_advice(rlp_table[2], Rotation::cur()),
                ),
                (
                    q_rlp_table * rpi_rlp,
                    meta.query_advice(rlp_table[3], Rotation::cur()),
                ),
            ]
        });

        meta.lookup_any(format_str!("lookup {name} keccak"), |meta| {
            let q_keccak_table = meta.query_selector(q_keccak_table);

            let rpi_rlp = meta.query_advice(rpi_rlp, Rotation::cur());
            let rpi_rlp_len = meta.query_advice(rpi_rlp_len, Rotation::cur());
            let rpi_keccak = meta.query_advice(rpi_keccak, Rotation::cur());
            vec![
                (
                    q_keccak_table.expr() * 1.expr(),
                    meta.query_advice(keccak_table.is_enabled, Rotation::cur()),
                ),
                (
                    q_keccak_table.expr() * rpi_rlp,
                    meta.query_advice(keccak_table.input_rlc, Rotation::cur()),
                ),
                (
                    q_keccak_table.expr() * rpi_rlp_len,
                    meta.query_advice(keccak_table.input_len, Rotation::cur()),
                ),
                (
                    q_keccak_table * rpi_keccak,
                    meta.query_advice(keccak_table.output_rlc, Rotation::cur()),
                ),
            ]
        });
    }
}

impl<F: Field> SubCircuitConfig<F> for PiCircuitConfig<F> {
    type ConfigArgs = PiCircuitConfigArgs<F>;

    /// Return a new PiCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            max_txs,
            max_calldata,
            block_table,
            tx_table,
            rlp_table,
            keccak_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        let q_block_table = meta.selector();
        let q_tx_table = meta.complex_selector();
        let q_tx_calldata = meta.complex_selector();
        let q_calldata_start = meta.complex_selector();

        let q_rlp_table = meta.complex_selector();
        let q_keccak_table = meta.complex_selector();

        // block
        let block = meta.advice_column();
        let block_rlc_acc = meta.advice_column();
        let block_rlp_len = meta.advice_column();
        let block_rlp = meta.advice_column();
        let block_keccak = meta.advice_column();
        let q_block_start = meta.selector();
        let q_block_not_end = meta.selector();

        // txlist
        let txs = meta.advice_column();
        let txs_rlc_acc = meta.advice_column();
        let txs_rlp_len = meta.advice_column();
        let txs_rlp = meta.advice_column();
        let txs_keccak = meta.advice_column();
        let q_txs_start = meta.selector();
        let q_txs_not_end = meta.selector();

        // Tx Table
        let tx_id = tx_table.tx_id;
        let tx_value = tx_table.value;
        let tag = tx_table.tag;
        let index = tx_table.index;
        let tx_id_inv = meta.advice_column();
        let tx_value_inv = meta.advice_column();
        let tx_id_diff_inv = meta.advice_column();
        // The difference of tx_id of adjacent rows in calldata part of tx table
        // lies in the interval [0, 2^16] if their tx_id both do not equal to zero.
        // We do not use 2^8 for the reason that a large block may have more than
        // 2^8 transfer transactions which have 21000*2^8 (~ 5.376M) gas.
        let fixed_u16 = meta.fixed_column();
        let calldata_gas_cost = meta.advice_column();
        let is_final = meta.advice_column();

        let pi = meta.instance_column();

        meta.enable_equality(block_rlc_acc);
        meta.enable_equality(block_keccak);
        meta.enable_equality(txs_rlc_acc);
        meta.enable_equality(txs_keccak);
        meta.enable_equality(pi);

        // block
        Self::constraint(
            meta,
            "block",
            q_block_start,
            q_block_not_end,
            block,
            block_rlc_acc,
            block_rlp_len,
            block_rlp,
            block_keccak,
            q_rlp_table,
            rlp_table,
            q_keccak_table,
            keccak_table,
            &challenges,
        );

        // txs
        Self::constraint(
            meta,
            "txs",
            q_txs_start,
            q_txs_not_end,
            txs,
            txs_rlc_acc,
            txs_rlp_len,
            txs_rlp,
            txs_keccak,
            q_rlp_table,
            rlp_table,
            q_keccak_table,
            keccak_table,
            &challenges,
        );

        // 0.2 Block table -> value column match with raw_public_inputs at expected
        // offset
        meta.create_gate("block_table[i] = block[i]", |meta| {
            let q_block_table = meta.query_selector(q_block_table);
            let block_value = meta.query_advice(block_table.value, Rotation::cur());
            let rpi_block_value = meta.query_advice(block, Rotation::cur());
            vec![q_block_table * (block_value - rpi_block_value)]
        });

        let tx_table_len = max_txs * TX_LEN + 1;

        //  0.3 Tx table -> {tx_id, index, value} column match with raw_public_inputs
        // at expected offset
        meta.create_gate("tx_table.tx_id[i] == txs[i]", |meta| {
            // row.q_tx_table * row.tx_table.tx_id
            // == row.q_tx_table * row_offset_tx_table_tx_id.raw_public_inputs
            let q_tx_table = meta.query_selector(q_tx_table);
            let tx_id = meta.query_advice(tx_table.tx_id, Rotation::cur());
            let rpi_tx_id = meta.query_advice(txs, Rotation::cur());

            vec![q_tx_table * (tx_id - rpi_tx_id)]
        });

        meta.create_gate("tx_table.index[i] == txs[tx_table_len + i]", |meta| {
            // row.q_tx_table * row.tx_table.tx_index
            // == row.q_tx_table * row_offset_tx_table_tx_index.raw_public_inputs
            let q_tx_table = meta.query_selector(q_tx_table);
            let tx_index = meta.query_advice(tx_table.index, Rotation::cur());
            let rpi_tx_index = meta.query_advice(txs, Rotation(tx_table_len as i32));

            vec![q_tx_table * (tx_index - rpi_tx_index)]
        });

        meta.create_gate("tx_table.tx_value[i] == txs[2* tx_table_len + i]", |meta| {
            // (row.q_tx_calldata | row.q_tx_table) * row.tx_table.tx_value
            // == (row.q_tx_calldata | row.q_tx_table) *
            // row_offset_tx_table_tx_value.raw_public_inputs
            let q_tx_table = meta.query_selector(q_tx_table);
            let tx_value = meta.query_advice(tx_value, Rotation::cur());
            let q_tx_calldata = meta.query_selector(q_tx_calldata);
            let rpi_tx_value = meta.query_advice(txs, Rotation((2 * tx_table_len) as i32));

            vec![or::expr([q_tx_table, q_tx_calldata]) * (tx_value - rpi_tx_value)]
        });

        let tx_id_is_zero_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_tx_calldata),
            |meta| meta.query_advice(tx_table.tx_id, Rotation::cur()),
            tx_id_inv,
        );
        let tx_value_is_zero_config = IsZeroChip::configure(
            meta,
            |meta| {
                or::expr([
                    meta.query_selector(q_tx_table),
                    meta.query_selector(q_tx_calldata),
                ])
            },
            |meta| meta.query_advice(tx_value, Rotation::cur()),
            tx_value_inv,
        );
        let _tx_id_diff_is_zero_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_tx_calldata),
            |meta| {
                meta.query_advice(tx_table.tx_id, Rotation::next())
                    - meta.query_advice(tx_table.tx_id, Rotation::cur())
            },
            tx_id_diff_inv,
        );

        meta.lookup_any("tx_id_diff", |meta| {
            let tx_id_next = meta.query_advice(tx_id, Rotation::next());
            let tx_id = meta.query_advice(tx_id, Rotation::cur());
            let tx_id_inv_next = meta.query_advice(tx_id_inv, Rotation::next());
            let tx_id_diff_inv = meta.query_advice(tx_id_diff_inv, Rotation::cur());
            let fixed_u16_table = meta.query_fixed(fixed_u16, Rotation::cur());

            let tx_id_next_nonzero = tx_id_next.expr() * tx_id_inv_next;
            let tx_id_not_equal_to_next = (tx_id_next.expr() - tx_id.expr()) * tx_id_diff_inv;
            let tx_id_diff_minus_one = tx_id_next - tx_id - 1.expr();

            vec![(
                tx_id_diff_minus_one * tx_id_next_nonzero * tx_id_not_equal_to_next,
                fixed_u16_table,
            )]
        });

        meta.create_gate("calldata constraints", |meta| {
            let q_is_calldata = meta.query_selector(q_tx_calldata);
            let q_calldata_start = meta.query_selector(q_calldata_start);
            let tx_idx = meta.query_advice(tx_id, Rotation::cur());
            let tx_idx_next = meta.query_advice(tx_id, Rotation::next());
            let tx_idx_inv_next = meta.query_advice(tx_id_inv, Rotation::next());
            let tx_idx_diff_inv = meta.query_advice(tx_id_diff_inv, Rotation::cur());
            let idx = meta.query_advice(index, Rotation::cur());
            let idx_next = meta.query_advice(index, Rotation::next());
            let value_next = meta.query_advice(tx_value, Rotation::next());
            let value_next_inv = meta.query_advice(tx_value_inv, Rotation::next());

            let gas_cost = meta.query_advice(calldata_gas_cost, Rotation::cur());
            let gas_cost_next = meta.query_advice(calldata_gas_cost, Rotation::next());
            let is_final = meta.query_advice(is_final, Rotation::cur());

            let is_tx_id_nonzero = not::expr(tx_id_is_zero_config.expr());
            let is_tx_id_next_nonzero = tx_idx_next.expr() * tx_idx_inv_next.expr();

            let is_value_zero = tx_value_is_zero_config.expr();
            let is_value_nonzero = not::expr(tx_value_is_zero_config.expr());

            let is_value_next_nonzero = value_next.expr() * value_next_inv.expr();
            let is_value_next_zero = not::expr(is_value_next_nonzero.expr());

            // gas = value == 0 ? 4 : 16
            let gas = ZERO_BYTE_GAS_COST.expr() * is_value_zero.expr()
                + NONZERO_BYTE_GAS_COST.expr() * is_value_nonzero.expr();
            let gas_next = ZERO_BYTE_GAS_COST.expr() * is_value_next_zero
                + NONZERO_BYTE_GAS_COST.expr() * is_value_next_nonzero;

            // if tx_id == 0 then idx == 0, tx_id_next == 0
            let default_calldata_row_constraint1 = tx_id_is_zero_config.expr() * idx.expr();
            let default_calldata_row_constraint2 = tx_id_is_zero_config.expr() * tx_idx_next.expr();
            let default_calldata_row_constraint3 = tx_id_is_zero_config.expr() * is_final.expr();
            let default_calldata_row_constraint4 = tx_id_is_zero_config.expr() * gas_cost.expr();

            // if tx_id != 0 then
            //    1. tx_id_next == tx_id: idx_next == idx + 1, gas_cost_next == gas_cost +
            //       gas_next, is_final == false;
            //    2. tx_id_next == tx_id + 1 + x (where x is in [0, 2^16)): idx_next == 0,
            //       gas_cost_next == gas_next, is_final == true;
            //    3. tx_id_next == 0: is_final == true, idx_next == 0, gas_cost_next == 0;
            // either case 1, case 2 or case 3 holds.

            let tx_id_equal_to_next =
                1.expr() - (tx_idx_next.expr() - tx_idx.expr()) * tx_idx_diff_inv.expr();
            let idx_of_same_tx_constraint =
                tx_id_equal_to_next.clone() * (idx_next.expr() - idx.expr() - 1.expr());
            let idx_of_next_tx_constraint = (tx_idx_next.expr() - tx_idx.expr()) * idx_next.expr();

            let gas_cost_of_same_tx_constraint = tx_id_equal_to_next.clone()
                * (gas_cost_next.expr() - gas_cost.expr() - gas_next.expr());
            let gas_cost_of_next_tx_constraint = is_tx_id_next_nonzero.expr()
                * (tx_idx_next.expr() - tx_idx.expr())
                * (gas_cost_next.expr() - gas_next.expr());

            let is_final_of_same_tx_constraint = tx_id_equal_to_next * is_final.expr();
            let is_final_of_next_tx_constraint =
                (tx_idx_next.expr() - tx_idx.expr()) * (is_final.expr() - 1.expr());

            // if tx_id != 0 then
            //    1. q_calldata_start * (index - 0) == 0 and
            //    2. q_calldata_start * (gas_cost - gas) == 0.

            vec![
                q_is_calldata.expr() * default_calldata_row_constraint1,
                q_is_calldata.expr() * default_calldata_row_constraint2,
                q_is_calldata.expr() * default_calldata_row_constraint3,
                q_is_calldata.expr() * default_calldata_row_constraint4,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * idx_of_same_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * idx_of_next_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * gas_cost_of_same_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * gas_cost_of_next_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * is_final_of_same_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * is_final_of_next_tx_constraint,
                q_calldata_start.expr() * is_tx_id_nonzero.expr() * (idx - 0.expr()),
                q_calldata_start.expr() * is_tx_id_nonzero.expr() * (gas_cost - gas),
            ]
        });

        // Test if tx tag equals to CallDataLength
        let tx_tag_is_cdl_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_tx_table),
            |meta| meta.query_fixed(tag, Rotation::cur()) - TxFieldTag::CallDataLength.expr(),
            tx_id_inv,
        );

        meta.create_gate(
            "call_data_gas_cost should be zero if call_data_length is zero",
            |meta| {
                let q_tx_table = meta.query_selector(q_tx_table);

                let is_calldata_length_zero = tx_value_is_zero_config.expr();
                let is_calldata_length_row = tx_tag_is_cdl_config.expr();
                let calldata_cost = meta.query_advice(tx_value, Rotation::next());

                vec![q_tx_table * is_calldata_length_row * is_calldata_length_zero * calldata_cost]
            },
        );

        meta.lookup_any("gas_cost in tx table", |meta| {
            let q_tx_table = meta.query_selector(q_tx_table);
            let is_final = meta.query_advice(is_final, Rotation::cur());

            let tx_id = meta.query_advice(tx_id, Rotation::cur());

            // calldata gas cost assigned in the tx table
            // CallDataGasCost is on the next row of CallDataLength
            let calldata_cost_assigned = meta.query_advice(tx_value, Rotation::next());
            // calldata gas cost calculated in call data
            let calldata_cost_calc = meta.query_advice(calldata_gas_cost, Rotation::cur());

            let is_calldata_length_row = tx_tag_is_cdl_config.expr();
            let is_calldata_length_nonzero = not::expr(tx_value_is_zero_config.expr());

            // lookup (tx_id, true, is_calldata_length_nonzero * is_calldata_cost *
            // gas_cost) in the table (tx_id, is_final, gas_cost)
            // if q_tx_table is true
            let condition = q_tx_table * is_calldata_length_nonzero * is_calldata_length_row;

            vec![
                (condition.expr() * tx_id.expr(), tx_id),
                (condition.expr() * 1.expr(), is_final),
                (
                    condition.expr() * calldata_cost_assigned,
                    calldata_cost_calc,
                ),
            ]
        });

        Self {
            max_txs,
            max_calldata,
            q_block_table,
            block_table,
            q_tx_table,
            q_tx_calldata,
            q_calldata_start,
            tx_table,
            tx_id_inv,
            tx_value_inv,
            tx_id_diff_inv,
            fixed_u16,
            calldata_gas_cost,
            is_final,
            pi,
            q_rlp_table,

            // rpi
            block,
            block_rlc_acc,
            block_rlp_len,
            block_rlp,
            block_keccak,
            q_block_start,
            q_block_not_end,

            // txlist
            txs,
            txs_rlc_acc,
            txs_rlp_len,
            txs_rlp,
            txs_keccak,
            q_txs_start,
            q_txs_not_end,

            rlp_table,
            q_keccak_table,
            keccak_table,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> PiCircuitConfig<F> {
    #[inline]
    fn circuit_block_len(&self) -> usize {
        // +1 empty row in block table, 1 row for rlc(hash(rlp(txlist)))
        // EXTRA_LEN: state_root, prev_root
        BLOCK_LEN + 1 + EXTRA_LEN + 1
    }

    #[inline]
    fn circuit_txs_len(&self) -> usize {
        3 * (TX_LEN * self.max_txs + 1) + self.max_calldata
    }

    fn assign_tx_empty_row(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        region.assign_advice(
            || "tx_id",
            self.tx_table.tx_id,
            offset,
            || Value::known(F::zero()),
        )?;
        region.assign_advice(
            || "tx_id_inv",
            self.tx_id_inv,
            offset,
            || Value::known(F::zero()),
        )?;
        region.assign_fixed(
            || "tag",
            self.tx_table.tag,
            offset,
            || Value::known(F::from(TxFieldTag::Null as u64)),
        )?;
        region.assign_advice(
            || "index",
            self.tx_table.index,
            offset,
            || Value::known(F::zero()),
        )?;
        region.assign_advice(
            || "tx_value",
            self.tx_table.value,
            offset,
            || Value::known(F::zero()),
        )?;
        region.assign_advice(
            || "tx_value_inv",
            self.tx_value_inv,
            offset,
            || Value::known(F::zero()),
        )?;
        region.assign_advice(
            || "is_final",
            self.is_final,
            offset,
            || Value::known(F::zero()),
        )?;
        region.assign_advice(
            || "gas_cost",
            self.calldata_gas_cost,
            offset,
            || Value::known(F::zero()),
        )?;
        Ok(())
    }
    /// Assigns a tx_table row and stores the values in a vec for the
    /// raw_public_inputs column
    #[allow(clippy::too_many_arguments)]
    fn assign_tx_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: usize,
        tag: TxFieldTag,
        index: usize,
        tx_value: Value<F>,
        raw_pi_vals: &mut [Value<F>],
    ) -> Result<(), Error> {
        let tx_id = F::from(tx_id as u64);
        // tx_id_inv = (tag - CallDataLength)^(-1)
        let tx_id_inv = if tag != TxFieldTag::CallDataLength {
            let x = F::from(tag as u64) - F::from(TxFieldTag::CallDataLength as u64);
            x.invert().unwrap_or(F::zero())
        } else {
            F::zero()
        };
        let tag = F::from(tag as u64);
        let index = F::from(index as u64);
        let tx_value = tx_value;
        let tx_value_inv = tx_value.map(|v| v.invert().unwrap_or(F::zero()));

        self.q_tx_table.enable(region, offset)?;

        // Assign vals to Tx_table
        region.assign_advice(
            || "tx_id",
            self.tx_table.tx_id,
            offset,
            || Value::known(tx_id),
        )?;
        region.assign_fixed(|| "tag", self.tx_table.tag, offset, || Value::known(tag))?;
        region.assign_advice(
            || "index",
            self.tx_table.index,
            offset,
            || Value::known(index),
        )?;
        region.assign_advice(|| "tx_value", self.tx_table.value, offset, || tx_value)?;
        region.assign_advice(
            || "tx_id_inv",
            self.tx_id_inv,
            offset,
            || Value::known(tx_id_inv),
        )?;
        region.assign_advice(
            || "tx_value_inverse",
            self.tx_value_inv,
            offset,
            || tx_value_inv,
        )?;

        // Assign vals to raw_public_inputs column
        let tx_table_len = TX_LEN * self.max_txs + 1;

        let index_offset = tx_table_len;
        let value_offset = index_offset + tx_table_len;

        region.assign_advice(|| "txlist.tx_id", self.txs, offset, || Value::known(tx_id))?;

        region.assign_advice(
            || "txlist.tx_index",
            self.txs,
            offset + index_offset,
            || Value::known(index),
        )?;

        region.assign_advice(
            || "txlist.tx_value",
            self.txs,
            offset + value_offset,
            || tx_value,
        )?;

        // Add copy to vec
        raw_pi_vals[offset] = Value::known(tx_id);
        raw_pi_vals[offset + index_offset] = Value::known(index);
        raw_pi_vals[offset + value_offset] = tx_value;

        Ok(())
    }

    /// Assigns one calldata row
    #[allow(clippy::too_many_arguments)]
    fn assign_tx_calldata_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: usize,
        tx_id_next: usize,
        index: usize,
        tx_value: F,
        is_final: bool,
        gas_cost: F,
        raw_pi_vals: &mut [Value<F>],
    ) -> Result<(), Error> {
        let tx_id = F::from(tx_id as u64);
        let tx_id_inv = tx_id.invert().unwrap_or(F::zero());
        let tx_id_diff = F::from(tx_id_next as u64) - tx_id;
        let tx_id_diff_inv = tx_id_diff.invert().unwrap_or(F::zero());
        let tag = F::from(TxFieldTag::CallData as u64);
        let index = F::from(index as u64);
        let tx_value = tx_value;
        let tx_value_inv = tx_value.invert().unwrap_or(F::zero());
        let is_final = if is_final { F::one() } else { F::zero() };

        // Assign vals to raw_public_inputs column
        let tx_table_len = TX_LEN * self.max_txs + 1;
        let calldata_offset = tx_table_len + offset;

        self.q_tx_calldata.enable(region, calldata_offset)?;

        // Assign vals to Tx_table
        region.assign_advice(
            || "tx_id",
            self.tx_table.tx_id,
            calldata_offset,
            || Value::known(tx_id),
        )?;
        region.assign_advice(
            || "tx_id_inv",
            self.tx_id_inv,
            calldata_offset,
            || Value::known(tx_id_inv),
        )?;
        region.assign_fixed(
            || "tag",
            self.tx_table.tag,
            calldata_offset,
            || Value::known(tag),
        )?;
        region.assign_advice(
            || "index",
            self.tx_table.index,
            calldata_offset,
            || Value::known(index),
        )?;
        region.assign_advice(
            || "tx_value",
            self.tx_table.value,
            calldata_offset,
            || Value::known(tx_value),
        )?;
        region.assign_advice(
            || "tx_value_inv",
            self.tx_value_inv,
            calldata_offset,
            || Value::known(tx_value_inv),
        )?;
        region.assign_advice(
            || "tx_id_diff_inv",
            self.tx_id_diff_inv,
            calldata_offset,
            || Value::known(tx_id_diff_inv),
        )?;
        region.assign_advice(
            || "is_final",
            self.is_final,
            calldata_offset,
            || Value::known(is_final),
        )?;
        region.assign_advice(
            || "gas_cost",
            self.calldata_gas_cost,
            calldata_offset,
            || Value::known(gas_cost),
        )?;

        let value_offset = 3 * tx_table_len;

        region.assign_advice(
            || "raw_pi.tx_value",
            self.txs,
            offset + value_offset,
            || Value::known(tx_value),
        )?;

        // Add copy to vec
        raw_pi_vals[offset + value_offset] = Value::known(tx_value);

        Ok(())
    }

    fn assign_block(
        &self,
        region: &mut Region<'_, F>,
        public_data: &PublicData,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let block_values = public_data.get_block_table_values();
        let extra_values = public_data.get_extra_values();
        let randomness = challenges.evm_word();
        self.q_block_start.enable(region, 0)?;
        let mut rlc_acc = Value::known(F::zero());
        for (offset, (name, val)) in [
            ("zero", Value::known(F::zero())),
            (
                "coinbase",
                Value::known(block_values.coinbase.to_scalar().unwrap()),
            ),
            ("gas_limit", Value::known(F::from(block_values.gas_limit))),
            ("number", Value::known(F::from(block_values.number))),
            ("timestamp", Value::known(F::from(block_values.timestamp))),
            (
                "difficulty",
                randomness.map(|randomness| rlc(block_values.difficulty.to_le_bytes(), randomness)),
            ),
            (
                "base_fee",
                randomness.map(|randomness| rlc(block_values.base_fee.to_le_bytes(), randomness)),
            ),
            ("chain_id", Value::known(F::from(block_values.chain_id))),
        ]
        .into_iter()
        .chain(
            block_values
                .history_hashes
                .iter()
                .map(|h| ("prev_hash", randomness.map(|v| rlc(h.to_fixed_bytes(), v)))),
        )
        .chain([
            // Assigns the extra fields (not in block or tx tables):
            //   - state root
            //   - previous block state root
            // to the raw_public_inputs column and stores a copy in a
            // vector for computing RLC(raw_public_inputs).
            (
                "state.root",
                randomness.map(|v| rlc(extra_values.state_root.to_fixed_bytes(), v)),
            ),
            (
                "parent_block.hash",
                randomness.map(|v| rlc(extra_values.prev_state_root.to_fixed_bytes(), v)),
            ),
        ])
        .enumerate()
        {
            self.q_block_table.enable(region, offset)?;
            self.q_block_not_end.enable(region, offset)?;
            region.assign_advice(|| name, self.block_table.value, offset, || val)?;
            region.assign_advice(|| name, self.block, offset, || val)?;
            rlc_acc = rlc_acc * randomness + val;
            region.assign_advice(|| name, self.block_rlc_acc, offset, || rlc_acc)?;
        }

        // last row
        let last = BLOCK_LEN + 1 + EXTRA_LEN;
        let (_, _, _, hash, _) = public_data.get_txs_rlp_and_hash(challenges);
        let (_, rlp_rlc, len, hash_rlc) = public_data.get_block_rlp_and_hash(hash, challenges);
        self.q_block_table.enable(region, last)?;
        region.assign_advice(|| "txs_hash", self.block_table.value, last, || hash_rlc)?;
        let txs_hash_cell = region.assign_advice(|| "txs_hash", self.block, last, || hash_rlc)?;
        rlc_acc = rlc_acc * randomness + hash_rlc;
        region.assign_advice(|| "txs_hash", self.block_rlc_acc, last, || rlc_acc)?;

        region.assign_advice(|| "txs_hash", self.block_rlp, last, || rlp_rlc)?;
        region.assign_advice(
            || "txs_hash",
            self.block_rlp_len,
            last,
            || Value::known(F::from(len as u64)),
        )?;
        let hash_cell =
            region.assign_advice(|| "txs_hash", self.block_keccak, last, || hash_rlc)?;
        Ok((hash_cell, txs_hash_cell))
    }

    // TODO:
    // 1. assign txs_rlp_len
    // 2. assign txs_keccak and return it
    fn assign_txs(
        &self,
        region: &mut Region<'_, F>,
        challenges: &Challenges<Value<F>>,
        rpi_vals: Vec<Value<F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.q_txs_start.enable(region, 0)?;

        let r = challenges.evm_word();

        let last = rpi_vals.len() - 1;
        let mut rlc_acc = Value::known(F::zero());
        // the last rpi_rlc == rpi_rlc_acc
        let mut rpi_rlc;
        // Next rows
        for (offset, val) in rpi_vals.iter().enumerate() {
            rlc_acc = rlc_acc * r + val;
            rpi_rlc = region.assign_advice(|| "rpi_rlc_acc", self.txs, offset, || rlc_acc)?;

            if offset != last {
                self.q_txs_not_end.enable(region, offset)?;
            }
        }

        Ok(rpi_rlc)
    }
}

/// Public Inputs Circuit
#[derive(Clone, Default, Debug)]
pub struct PiCircuit<F: Field> {
    max_txs: usize,
    max_calldata: usize,
    /// PublicInputs data known by the verifier
    pub public_data: PublicData,

    block: Block<F>,

    _marker: PhantomData<F>,
}

impl<F: Field> PiCircuit<F> {
    /// Creates a new PiCircuit
    pub fn new(
        max_txs: usize,
        max_calldata: usize,
        public_data: PublicData,
        block: Block<F>,
    ) -> Self {
        Self {
            max_txs,
            max_calldata,
            public_data,
            block,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> SubCircuit<F> for PiCircuit<F> {
    type Config = PiCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        let public_data = PublicData {
            chain_id: block.context.chain_id,
            history_hashes: block.context.history_hashes.clone(),
            transactions: block.eth_block.transactions.clone(),
            state_root: block.eth_block.state_root,
            prev_state_root: H256::from_uint(&block.prev_state_root),
            block_constants: BlockConstants {
                coinbase: block.context.coinbase,
                timestamp: block.context.timestamp,
                number: block.context.number.as_u64().into(),
                difficulty: block.context.difficulty,
                gas_limit: block.context.gas_limit.into(),
                base_fee: block.context.base_fee,
            },
            block_ctx: block.context,
        };
        PiCircuit::new(
            block.circuits_params.max_txs,
            block.circuits_params.max_calldata,
            public_data,
            block.clone(),
        )
    }

    /// Compute the public inputs for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        vec![]
    }

    /// Make the assignments to the PiCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed u16 table",
            |mut region| {
                for i in 0..(1 << 16) {
                    region.assign_fixed(
                        || format!("row_{}", i),
                        config.fixed_u16,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }

                Ok(())
            },
        )?;
        let hash_cell = layouter.assign_region(
            || "region 0",
            |mut region| {
                // Assign block table
                let (hash_cell, txs_hash_cell) =
                    config.assign_block(&mut region, &self.public_data, challenges)?;

                // Assign Tx table
                let mut offset = 0;
                let txs = self.public_data.get_tx_table_values();
                assert!(txs.len() <= config.max_txs);
                let tx_default = TxValues::default();

                let circuit_len = config.circuit_block_len();
                let mut rpi_vals = vec![Value::known(F::zero()); circuit_len];

                // Add empty row
                config.assign_tx_row(
                    &mut region,
                    offset,
                    0,
                    TxFieldTag::Null,
                    0,
                    Value::known(F::zero()),
                    &mut rpi_vals,
                )?;
                offset += 1;

                let randomness = challenges.evm_word();

                for i in 0..config.max_txs {
                    let tx = if i < txs.len() { &txs[i] } else { &tx_default };

                    for (tag, value) in &[
                        (
                            TxFieldTag::Nonce,
                            randomness.map(|randomness| rlc(tx.nonce.to_le_bytes(), randomness)),
                        ),
                        (
                            TxFieldTag::Gas,
                            randomness.map(|randomness| rlc(tx.gas.to_le_bytes(), randomness)),
                        ),
                        (
                            TxFieldTag::GasPrice,
                            randomness.map(|v| rlc(tx.gas_price.to_le_bytes(), v)),
                        ),
                        (
                            TxFieldTag::CallerAddress,
                            Value::known(tx.from_addr.to_scalar().expect("tx.from too big")),
                        ),
                        (
                            TxFieldTag::CalleeAddress,
                            Value::known(tx.to_addr.to_scalar().expect("tx.to too big")),
                        ),
                        (TxFieldTag::IsCreate, Value::known(F::from(tx.is_create))),
                        (
                            TxFieldTag::Value,
                            randomness.map(|randomness| rlc(tx.value.to_le_bytes(), randomness)),
                        ),
                        (
                            TxFieldTag::CallDataLength,
                            Value::known(F::from(tx.call_data_len)),
                        ),
                        (
                            TxFieldTag::CallDataGasCost,
                            Value::known(F::from(tx.call_data_gas_cost)),
                        ),
                        (
                            TxFieldTag::TxSignHash,
                            randomness.map(|randomness| rlc(tx.tx_sign_hash, randomness)),
                        ),
                    ] {
                        config.assign_tx_row(
                            &mut region,
                            offset,
                            i + 1,
                            *tag,
                            0,
                            *value,
                            &mut rpi_vals,
                        )?;
                        offset += 1;
                    }
                }
                // Tx Table CallData
                let mut calldata_count = 0;
                config.q_calldata_start.enable(&mut region, offset)?;
                // the call data bytes assignment starts at offset 0
                offset = 0;
                let txs = self.public_data.txs();
                for (i, tx) in self.public_data.txs().iter().enumerate() {
                    let call_data_length = tx.call_data.0.len();
                    let mut gas_cost = F::zero();
                    for (index, byte) in tx.call_data.0.iter().enumerate() {
                        assert!(calldata_count < config.max_calldata);
                        let is_final = index == call_data_length - 1;
                        gas_cost += if *byte == 0 {
                            F::from(ZERO_BYTE_GAS_COST)
                        } else {
                            F::from(NONZERO_BYTE_GAS_COST)
                        };
                        let tx_id_next = if is_final {
                            let mut j = i + 1;
                            while j < txs.len() && txs[j].call_data.0.is_empty() {
                                j += 1;
                            }
                            if j >= txs.len() {
                                0
                            } else {
                                j + 1
                            }
                        } else {
                            i + 1
                        };

                        config.assign_tx_calldata_row(
                            &mut region,
                            offset,
                            i + 1,
                            tx_id_next as usize,
                            index,
                            F::from(*byte as u64),
                            is_final,
                            gas_cost,
                            &mut rpi_vals,
                        )?;
                        offset += 1;
                        calldata_count += 1;
                    }
                }
                for _ in calldata_count..config.max_calldata {
                    config.assign_tx_calldata_row(
                        &mut region,
                        offset,
                        0, // tx_id
                        0,
                        0,
                        F::zero(),
                        false,
                        F::zero(),
                        &mut rpi_vals,
                    )?;
                    offset += 1;
                }
                // NOTE: we add this empty row so as to pass mock prover's check
                //      otherwise it will emit CellNotAssigned Error
                let tx_table_len = TX_LEN * self.max_txs + 1;
                config.assign_tx_empty_row(&mut region, tx_table_len + offset)?;
                let origin_txs_hash_cell = config.assign_txs(&mut region, challenges, rpi_vals)?;
                // assert two txs hash are equal
                region.constrain_equal(txs_hash_cell.cell(), origin_txs_hash_cell.cell())?;
                Ok(hash_cell)
            },
        )?;

        // Constrain hash value of block to public inputs
        layouter.constrain_instance(hash_cell.cell(), config.pi, 0)?;

        Ok(())
    }
}

// We define the PiTestCircuit as a wrapper over PiCircuit extended to take the
// generic const parameters MAX_TXS and MAX_CALLDATA.  This is necessary because
// the trait Circuit requires an implementation of `configure` that doesn't take
// any circuit parameters, and the PiCircuit defines gates that use rotations
// that depend on MAX_TXS and MAX_CALLDATA, so these two values are required
// during the configuration.
/// Test Circuit for PiCircuit
#[cfg(any(feature = "test", test))]
#[derive(Default, Clone)]
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
        let rlp_table = array_init::array_init(|_| meta.advice_column());
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);
        (
            PiCircuitConfig::new(
                meta,
                PiCircuitConfigArgs {
                    max_txs: MAX_TXS,
                    max_calldata: MAX_CALLDATA,
                    block_table,
                    tx_table,
                    rlp_table,
                    keccak_table,
                    challenges: challenge_exprs,
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
        // assign block table
        config
            .block_table
            .load(&mut layouter, &self.0.public_data.block_ctx, &challenges)?;
        // assign tx table
        config.tx_table.load(
            &mut layouter,
            &self.0.block.txs,
            self.0.max_txs,
            &challenges,
        )?;
        let (txs_rlp, txs_rlp_rlc, txs_len, hash, _) =
            self.0.public_data.get_txs_rlp_and_hash(&challenges);
        let (block_rlp, block_rlp_rlc, block_len, _) =
            self.0.public_data.get_block_rlp_and_hash(hash, &challenges);
        // assign rlp table
        layouter.assign_region(
            || "rlp table",
            |region| {
                for (offset, vals) in [
                    [
                        Value::known(F::one()),
                        self.0.public_data.get_txs_rlc(),
                        txs_rlp_rlc,
                        Value::known(F::from(txs_len as u64)),
                    ],
                    [
                        Value::known(F::one()),
                        self.0.public_data.get_block_rlc(),
                        block_rlp_rlc,
                        Value::known(F::from(block_len as u64)),
                    ],
                ]
                .iter()
                .enumerate()
                {
                    for (val, row) in vals.iter().zip_eq(config.rlp_table.iter()) {
                        region.assign_advice(|| "", *row, 0, || *val)?;
                    }
                }
                Ok(())
            },
        )?;
        // assign keccak table
        config.keccak_table.dev_load(
            &mut layouter,
            vec![&txs_rlp.to_vec(), &block_rlp.to_vec()],
            &challenges,
        )?;

        self.0.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

#[cfg(test)]
mod pi_circuit_test {
    use super::*;

    use crate::test_util::rand_tx;
    use halo2_proofs::{
        dev::{MockProver, VerifyFailure},
        halo2curves::bn256::Fr,
    };
    use pretty_assertions::assert_eq;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

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
}
