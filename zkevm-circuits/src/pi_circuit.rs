//! Public Input Circuit implementation

// TODO disallow unused imports
#![allow(unused_imports)]
use std::marker::PhantomData;

use eth_types::geth_types::BlockConstants;
use eth_types::{geth_types::GethData, U256, U64};
use eth_types::{
    geth_types::Transaction, Address, Field, ToBigEndian, ToLittleEndian, ToScalar, Word,
};
use eth_types::{Bytes, H256};
use ethers_core::abi::ethereum_types::H160;
use ethers_core::types::Block;

use crate::tx_circuit::TxFieldTag;
use crate::util::random_linear_combine_word as rlc;
use crate::util::Expr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

/// Fixed by the spec TODO Review
const TX_LEN: usize = 8;
const BLOCK_LEN: usize = 7 + 256;
const EXTRA_LEN: usize = 3;

/// Values of the block table (as in the spec)
#[derive(Clone, Default, Debug)]
pub struct BlockValues {
    //First 6 fields correspond to geth_types::BlockConstants

    // hash: U256,
    // parent_hash: U256,
    // uncle_hash: U256,
    coinbase: Address, // Check if this is an apropriate type
    // root: U256,           // State Trie Root,
    // tx_hash: U256,        // Txs Trie Root,
    // receipt_hash: U256,   // Receipts Trie Root,
    // bloom: Option<Bloom>, // 256 bytes,
    gas_limit: Word,
    number: u64,
    timestamp: Word,
    difficulty: Word,
    base_fee: Word, // NOTE: BaseFee was added by EIP-1559 and is ignored in legacy headers.
    // gas_used: U64,
    // extra: Vec<u8>, // NOTE: We assume this is always an empty byte array,
    // mix_digest: U256,
    // nonce: U64,
    chain_id: Word,
    history_hashes: Vec<U256>,
}

/// Values of the tx table (as in the spec)
#[derive(Default, Debug, Clone)]
pub struct TxValues {
    nonce: Word,
    gas: Word, //gas limit
    gas_price: Word,
    // gas_tip_cap: Word;
    // gas_fee_cap: Word;
    from_addr: Address,
    to_addr: Address,
    is_create: u64,
    value: Word,
    call_data_len: u64,
    /* TODO figure this one out
     * tx_sign_hash: U256, */
}

/// PublicData contains all the values that the PiCircuit recieves as input
#[derive(Debug, Clone)]
pub struct PublicData {
    txs: Vec<Transaction>,
    extra: GethData,                 //contains Block + extra fields {}
    block_constants: BlockConstants, // may not be necessary
    block_prev_root: Word,
}

impl Default for PublicData {
    fn default() -> Self {
        let geth_data = GethData {
            chain_id: Word::default(),
            history_hashes: Vec::default(),
            eth_block: Block::default(),
            geth_traces: Vec::default(),
            accounts: Vec::default(),
        };
        Self {
            txs: Vec::new(),
            extra: geth_data,
            block_constants: BlockConstants::default(),
            block_prev_root: Word::default(),
        }
    }
}

impl PublicData {
    /// Returns struct with values for the block table
    pub fn get_block_table_values(&self) -> BlockValues {
        BlockValues {
            coinbase: self.block_constants.coinbase,
            gas_limit: self.block_constants.gas_limit,
            number: self.block_constants.number.as_u64(),
            timestamp: self.block_constants.timestamp,
            difficulty: self.block_constants.difficulty,
            base_fee: self.block_constants.base_fee,
            chain_id: self.extra.chain_id,
            history_hashes: self.extra.history_hashes.clone(),
        }
    }

    /// Returns struct with values for the tx table
    pub fn get_tx_table_values(&self) -> Vec<TxValues> {
        let mut tx_vals = vec![];
        for tx in &self.txs {
            tx_vals.push(TxValues {
                nonce: tx.nonce,
                gas_price: tx.gas_price,
                gas: tx.gas_limit, //gas limit
                from_addr: tx.from,
                to_addr: tx.to.unwrap_or_else(Address::zero),
                is_create: (tx.to.is_none() as u64),
                value: tx.value,
                call_data_len: (tx.call_data.0.len() as u64).into(),
                // tx_sign_hash: tx.tx_sign_hash,
            });
        }
        tx_vals
    }
}

/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct PiCircuitConfig<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    q_block_table: Selector,
    block_value: Column<Advice>,

    q_tx_table: Selector,
    tx_id: Column<Advice>,
    tag: Column<Fixed>,
    index: Column<Advice>,
    tx_value: Column<Advice>,

    raw_public_inputs: Column<Advice>,
    rpi_rlc_acc: Column<Advice>,
    rand_rpi: Column<Advice>,
    q_end: Selector,

    _marker: PhantomData<F>,
    /*TODO add PI col
     * should contain: p, rand_rpi + extra fields: chaindID, block.root, block.hash,
     * prevblock.hashes */
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>
    PiCircuitConfig<F, MAX_TXS, MAX_CALLDATA>
{
    fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let q_block_table = meta.selector();
        // BlockTable
        let block_value = meta.advice_column();

        let q_tx_table = meta.selector();
        // Tx Table
        let tx_id = meta.advice_column();
        let tag = meta.fixed_column();
        let index = meta.advice_column();
        let tx_value = meta.advice_column();

        let raw_public_inputs = meta.advice_column();
        let rpi_rlc_acc = meta.advice_column();
        let rand_rpi = meta.advice_column();
        let q_end = meta.selector();

        // TODO enable equalities
        meta.enable_equality(raw_public_inputs);
        meta.enable_equality(rpi_rlc_acc);
        meta.enable_equality(rand_rpi);

        // TODO declare instances -> pi

        // 0.0 rpi_rlc_acc[0] == RLC(raw_public_inputs, rand_rpi)
        meta.create_gate("rpi_rlc_acc = RLC(raw_public_inputs, rand_rpi)", |meta| {
            // row.rpi_rlc_acc == q_not_end * row_next.rpi_rlc_acc * row.rand_rpi +
            // row.raw_public_inputs
            let q_not_end = 1u64.expr() - meta.query_selector(q_end);
            let cur_rpi_rlc_acc = meta.query_advice(rpi_rlc_acc, Rotation::cur());
            let next_rpi_rlc_acc = meta.query_advice(rpi_rlc_acc, Rotation::next());
            let rand_rpi = meta.query_advice(rand_rpi, Rotation::cur());
            let raw_public_inputs = meta.query_advice(raw_public_inputs, Rotation::cur());

            vec![q_not_end * next_rpi_rlc_acc * rand_rpi + raw_public_inputs - cur_rpi_rlc_acc]
        });

        // 0.1 rand_rpi[i] == rand_rpi[j]
        meta.create_gate("rand_pi = rand_rpi.next", |meta| {
            // q_not_end * row.rand_rpi == q_not_end * row_next.rand_rpi
            let q_not_end = 1u64.expr() - meta.query_selector(q_end);
            let cur_rand_rpi = meta.query_advice(rand_rpi, Rotation::cur());
            let next_rand_rpi = meta.query_advice(rand_rpi, Rotation::next());

            vec![q_not_end * (cur_rand_rpi - next_rand_rpi)]
        });

        let offset = BLOCK_LEN + EXTRA_LEN;
        let tx_table_len = MAX_TXS * TX_LEN + MAX_CALLDATA;

        //  0.3 Tx table -> {tx_id, index, value} column match with raw_public_inputs at
        // expected offset
        meta.create_gate("", |meta| {
            // row.q_tx_table * row.tx_table.tx_id
            // == row.q_tx_table * row_offset_tx_table_tx_id.raw_public_inputs
            let q_tx_table = meta.query_selector(q_tx_table);
            let tx_id = meta.query_advice(tx_id, Rotation::cur());
            let rpi_tx_id = meta.query_advice(raw_public_inputs, Rotation(offset as i32));

            vec![q_tx_table * (tx_id - rpi_tx_id)]
        });

        meta.create_gate("", |meta| {
            // row.q_tx_table * row.tx_table.tx_index
            // == row.q_tx_table * row_offset_tx_table_tx_index.raw_public_inputs
            let q_tx_table = meta.query_selector(q_tx_table);
            let tx_index = meta.query_advice(index, Rotation::cur());
            let rpi_tx_index =
                meta.query_advice(raw_public_inputs, Rotation((offset + tx_table_len) as i32));

            vec![q_tx_table * (tx_index - rpi_tx_index)]
        });

        meta.create_gate("", |meta| {
            // row.q_tx_table * row.tx_table.tx_value
            // == row.q_tx_table * row_offset_tx_table_tx_value.raw_public_inputs
            let q_tx_table = meta.query_selector(q_tx_table);
            let tx_value = meta.query_advice(tx_value, Rotation::cur());
            let rpi_tx_value = meta.query_advice(
                raw_public_inputs,
                Rotation((offset + 2 * tx_table_len) as i32),
            );

            vec![q_tx_table * (tx_value - rpi_tx_value)]
        });

        meta.create_gate("", |meta| {
            let q_block_table = meta.query_selector(q_block_table);
            let block_value = meta.query_advice(block_value, Rotation::cur());
            let rpi_block_value = meta.query_advice(raw_public_inputs, Rotation::cur());
            vec![q_block_table * (block_value - rpi_block_value)]
        });

        Self {
            q_block_table,
            block_value,
            q_tx_table,
            tx_id,
            tag,
            index,
            tx_value,
            raw_public_inputs,
            rpi_rlc_acc,
            rand_rpi,
            q_end,
            _marker: PhantomData,
        }
    }

    /// Assigns a tx_table row and its copy in the raw_public_inputs column
    fn assign_tx_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: usize,
        tag: TxFieldTag,
        index: usize,
        tx_value: F,
    ) -> Result<(), Error> {
        let tx_id = F::from(tx_id as u64);
        let tag = F::from(tag as u64);
        let index = F::from(index as u64);
        let tx_value = tx_value;

        self.q_tx_table.enable(region, offset)?;
        // tx_table assign
        region.assign_advice(|| "tx_id", self.tx_id, offset, || Ok(tx_id))?;
        region.assign_fixed(|| "tag", self.tag, offset, || Ok(tag))?;
        region.assign_advice(|| "index", self.index, offset, || Ok(index))?;
        region.assign_advice(|| "tx_value", self.tx_value, offset, || Ok(tx_value))?;

        // raw_public_inputs assign
        let tx_table_len = TX_LEN * MAX_TXS + MAX_CALLDATA;

        let id_offset = BLOCK_LEN + EXTRA_LEN;
        let index_offset = id_offset + tx_table_len;
        let value_offset = index_offset + tx_table_len;

        region.assign_advice(
            || "raw_pi.tx_id",
            self.raw_public_inputs,
            offset + id_offset,
            || Ok(tx_id),
        )?;

        region.assign_advice(
            || "raw_pi.tx_index",
            self.raw_public_inputs,
            offset + index_offset,
            || Ok(index),
        )?;

        region.assign_advice(
            || "raw_pi.tx_value",
            self.raw_public_inputs,
            offset + value_offset,
            || Ok(tx_value),
        )?;

        Ok(())
    }

    /// Assigns the values for block table and ints copy in the
    /// raw_public_inputs column
    fn assign_block_table(
        &self,
        region: &mut Region<'_, F>,
        mut offset: usize,
        block_values: BlockValues,
        randomness: F,
    ) -> Result<(), Error> {
        for i in 0..BLOCK_LEN {
            self.q_block_table.enable(region, offset + i)?;
        }

        let mut coinbase_bytes = [0u8; 32];
        coinbase_bytes[12..].clone_from_slice(block_values.coinbase.as_bytes());
        region.assign_advice(
            || "coinbase",
            self.block_value,
            offset,
            || Ok(rlc(coinbase_bytes, randomness)),
        )?;
        offset += 1;

        region.assign_advice(
            || "gas_limit",
            self.block_value,
            offset,
            || Ok(rlc(block_values.gas_limit.to_le_bytes(), randomness)),
        )?;
        offset += 1;

        region.assign_advice(
            || "number",
            self.block_value,
            offset,
            || Ok(F::from(block_values.number)),
        )?;
        offset += 1;

        region.assign_advice(
            || "timestamp",
            self.block_value,
            offset,
            || Ok(rlc(block_values.timestamp.to_le_bytes(), randomness)),
        )?;
        offset += 1;

        region.assign_advice(
            || "difficulty",
            self.block_value,
            offset,
            || Ok(rlc(block_values.difficulty.to_le_bytes(), randomness)),
        )?;
        offset += 1;

        region.assign_advice(
            || "base_fee",
            self.block_value,
            offset,
            || Ok(rlc(block_values.base_fee.to_le_bytes(), randomness)),
        )?;
        offset += 1;

        region.assign_advice(
            || "chain_id",
            self.block_value,
            offset,
            || Ok(rlc(block_values.chain_id.to_le_bytes(), randomness)),
        )?;
        offset += 1;

        for prev_hash in block_values.history_hashes {
            region.assign_advice(
                || "prev_hash",
                self.block_value,
                offset,
                || Ok(rlc(prev_hash.to_le_bytes(), randomness)),
            )?;
            offset += 1;
        }

        Ok(())
    }
}

/// TODO doc
#[derive(Default)]
pub struct PiCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    // no chips
    /// Randomness for RLC encdoing
    pub randomness: F,

    /// Randomness for PI encoding
    pub rand_rpi: F,

    /// TODO doc
    pub public_data: PublicData,
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> Circuit<F>
    for PiCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    type Config = PiCircuitConfig<F, MAX_TXS, MAX_CALLDATA>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        PiCircuitConfig::new(meta)
    }

    // synthesize
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let txs = self.public_data.get_tx_table_values();
        assert!(txs.len() < MAX_TXS);

        layouter.assign_region(
            || "",
            |mut region| {
                let mut offset = 0;
                let tx_default = TxValues::default();

                // TODO add an empty row?
                // Tx table
                for i in 0..MAX_TXS {
                    let tx = if i < txs.len() { &txs[i] } else { &tx_default };

                    for (tag, value) in &[
                        (
                            TxFieldTag::Nonce,
                            rlc(tx.nonce.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::Gas,
                            rlc(tx.gas.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::GasPrice,
                            rlc(tx.gas_price.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::CallerAddress,
                            tx.from_addr.to_scalar().expect("tx.from too big"),
                        ),
                        (
                            TxFieldTag::CalleeAddress,
                            tx.to_addr.to_scalar().expect("tx.to too big"),
                        ),
                        (
                            TxFieldTag::Value,
                            rlc(tx.value.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::CallDataLength,
                            F::from(tx.call_data_len),
                        ),
                        // TODO
                        // (
                        //     TxFieldTag::TxSignHash,
                        //     // *msg_hash_rlc_value.unwrap_or(&F::zero()),
                        // ),
                    ] {
                        config.assign_tx_row(&mut region, offset, i + 1, *tag, 0, *value)?;

                        offset += 1;
                    }
                }
                // Tx Table CallData
                let mut calldata_count = 0;
                for (i, tx) in self.public_data.txs.iter().enumerate() {
                    for (index, byte) in tx.call_data.0.iter().enumerate() {
                        assert!(calldata_count < MAX_CALLDATA);
                        config.assign_tx_row(
                            &mut region,
                            offset,
                            i + 1,
                            TxFieldTag::CallData,
                            index,
                            F::from(*byte as u64),
                        )?;
                        offset += 1;
                        calldata_count += 1;
                    }
                }
                for _ in calldata_count..MAX_CALLDATA {
                    config.assign_tx_row(
                        &mut region,
                        offset,
                        0, // tx_id
                        TxFieldTag::CallData,
                        0,
                        F::zero(),
                    )?;
                    offset += 1;
                }

                // Assign block table
                offset = 0;
                let block_values = self.public_data.get_block_table_values();
                config.assign_block_table(&mut region, offset, block_values, self.randomness)?;

                // Assign extra fields in raw_inputs
                offset += BLOCK_LEN;
                region.assign_advice(
                    || "block.hash",
                    config.raw_public_inputs,
                    offset,
                    || {
                        Ok(rlc(
                            self.public_data
                                .extra
                                .eth_block
                                .hash
                                .unwrap() // TODO review
                                .to_fixed_bytes(),
                            self.randomness,
                        ))
                    },
                )?;
                offset += 1;

                region.assign_advice(
                    || "block.root",
                    config.raw_public_inputs,
                    offset,
                    || {
                        Ok(rlc(
                            self.public_data.extra.eth_block.state_root.to_fixed_bytes(),
                            self.randomness,
                        ))
                    },
                )?;
                offset += 1;

                region.assign_advice(
                    || "block.hash",
                    config.raw_public_inputs,
                    offset,
                    || {
                        Ok(rlc(
                            self.public_data
                                .extra
                                .eth_block
                                .parent_hash
                                .to_fixed_bytes(),
                            self.randomness,
                        ))
                    },
                )?;

                let tx_table_len = TX_LEN * MAX_TXS + MAX_CALLDATA;
                offset += 3 * tx_table_len;
                config.q_end.enable(&mut region, offset);

                // TODO PI stuff
                Ok(())
            },
        )?;
        Ok(())
    }
}

// /// Block header
// #[derive(Clone, Default)]
// pub struct Block {
//     hash: U256,
//     parent_hash: U256,
//     uncle_hash: U256,
//     coinbase: H160,       // Check if this is an apropriate type
//     root: U256,           // State Trie Root,
//     tx_hash: U256,        // Txs Trie Root,
//     receipt_hash: U256,   // Receipts Trie Root,
//     bloom: Option<Bloom>, // 256 bytes,
//     difficulty: U256,
//     number: U64,
//     gas_limit: U64,
//     gas_used: U64,
//     time: U64,
//     extra: Vec<u8>, // NOTE: We assume this is always an empty byte array,
//     mix_digest: U256,
//     nonce: U64,
//     base_fee: U256, // NOTE: BaseFee was added by EIP-1559 and is ignored in
// legacy headers.; }

// #[derive(Clone, Default)]
// pub struct Transaction {
//     nonce: U64,
//     gas_price: U256,
//     gas: U64,
//     from_addr: H160,
//     to_addr: H160,
//     value: U256,
//     data: Vec<u8>,
//     tx_sign_hash: U256,
// }

#[cfg(test)]
mod pi_circuit_test {
    use halo2_proofs::dev::MockProver;

    use super::*;

    // fn rand_tx() -> Transaction {
    //     let nonce =
    // }

    fn test_basic() {
        let MAX_TXS = 2;
        let MAX_CALL_DATA_BYTES = 8;

        // public_data = rand_public_data(MAX_TXS-1, MAX_CALL_DATA_BYTES)
        // verify(public_data, MAX_TXS, MAX_CALLDATA_BYTES, rand_rpi)
    }

    fn verify<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(k: u32, success: bool) {
        let circuit = PiCircuit::<F, MAX_TXS, MAX_CALLDATA> {
            // size: 2usize.pow(k),
            rand_rpi: F::zero(),
            txs: vec![],
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let err = prover.verify();
        let print_failures = true;
        if err.is_err() && print_failures {
            for e in err.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }
    // TODO Some aux fn to generate random blocks and tx
}
