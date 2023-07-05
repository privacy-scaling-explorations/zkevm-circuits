//! The instance definition.

use eth_types::{geth_types::BlockConstants, BigEndianHash, Field, Keccak};
use std::{iter, ops::Deref};

use eth_types::{geth_types::Transaction, Address, ToBigEndian, Word, H256};
use itertools::Itertools;

use crate::{util::word, witness::Block};

pub(super) const ZERO_BYTE_GAS_COST: u64 = 4;
pub(super) const NONZERO_BYTE_GAS_COST: u64 = 16;

/// Values of the block table (as in the spec)
#[derive(Clone, Default, Debug)]
pub struct BlockValues {
    /// coinbase
    pub coinbase: Address,
    /// gas_limit
    pub gas_limit: u64,
    /// number
    pub number: u64,
    /// timestamp
    pub timestamp: u64,
    /// difficulty
    pub difficulty: Word,
    /// base_fee
    pub base_fee: Word, // NOTE: BaseFee was added by EIP-1559 and is ignored in legacy headers.
    /// chain_id
    pub chain_id: u64,
    /// history_hashes
    pub history_hashes: Vec<H256>,
}

/// Values of the tx table (as in the spec)
#[derive(Default, Debug, Clone)]
pub struct TxValues {
    /// nonce
    pub nonce: u64,
    /// gas_limit
    pub gas_limit: u64,
    /// gas_price
    pub gas_price: Word,
    /// from_addr
    pub from_addr: Address,
    /// to_addr
    pub to_addr: Address,
    /// is_create
    pub is_create: u64,
    /// value
    pub value: Word,
    /// call_data_len
    pub call_data_len: u64,
    /// call_data_gas_cost
    pub call_data_gas_cost: u64,
    /// tx_sign_hash
    pub tx_sign_hash: [u8; 32],
}

/// Extra values (not contained in block or tx tables)
#[derive(Default, Debug, Clone)]
pub struct ExtraValues {
    /// block_hash
    pub block_hash: H256,
    /// state_root
    pub state_root: H256,
    /// prev_state_root
    pub prev_state_root: H256,
}

/// PublicData contains all the values that the PiCircuit recieves as input
#[derive(Debug, Clone)]
pub struct PublicData {
    /// chain id
    pub chain_id: Word,
    /// History hashes contains the most recent 256 block hashes in history,
    /// where the latest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// Block Transactions
    pub transactions: Vec<Transaction>,
    /// Block State Root
    pub state_root: H256,
    /// Previous block root
    pub prev_state_root: H256,
    /// Constants related to Ethereum block
    pub block_constants: BlockConstants,
    /// Block Hash
    pub block_hash: Option<H256>,
}

impl Default for PublicData {
    fn default() -> Self {
        PublicData {
            chain_id: Word::default(),
            history_hashes: vec![],
            transactions: vec![],
            state_root: H256::zero(),
            prev_state_root: H256::zero(),
            block_constants: BlockConstants::default(),
            block_hash: None,
        }
    }
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
        for tx in &self.transactions {
            let sign_data_res = tx.sign_data(chain_id);
            let msg_hash_le =
                sign_data_res.map_or_else(|_| [0u8; 32], |sign_data| sign_data.msg_hash.to_bytes());
            tx_vals.push(TxValues {
                nonce: tx.nonce.low_u64(),
                gas_price: tx.gas_price,
                gas_limit: tx.gas(),
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

    /// Returns struct with the extra values
    pub fn get_extra_values(&self) -> ExtraValues {
        ExtraValues {
            block_hash: self.block_hash.unwrap_or_else(H256::zero),
            state_root: self.state_root,
            prev_state_root: self.prev_state_root,
        }
    }

    /// get the serialized public data bytes
    pub fn get_pi_bytes(&self, max_txs: usize, max_calldata: usize) -> Vec<u8> {
        // Assign block table
        let block_values = self.get_block_table_values();
        let result = iter::empty()
            .chain(0u8.to_be_bytes()) // zero byte
            .chain(block_values.coinbase.to_fixed_bytes()) // coinbase
            .chain(block_values.gas_limit.to_be_bytes()) // gas_limit
            .chain(block_values.number.to_be_bytes()) // number
            .chain(block_values.timestamp.to_be_bytes()) // timestamp
            .chain(block_values.difficulty.to_be_bytes()) // difficulty
            .chain(block_values.base_fee.to_be_bytes()) // base_fee
            .chain(block_values.chain_id.to_be_bytes()) // chain_id
            .chain(
                block_values
                    .history_hashes
                    .iter()
                    .flat_map(|prev_hash| prev_hash.to_fixed_bytes()),
            ); // history_hashes

        // Assign extra fields
        let extra_vals = self.get_extra_values();
        let result = result
            .chain(extra_vals.block_hash.to_fixed_bytes()) // block hash
            .chain(extra_vals.state_root.to_fixed_bytes()) // block state root
            .chain(extra_vals.prev_state_root.to_fixed_bytes()); // previous block state root

        // Assign Tx table
        let tx_field_byte_fn = |tx_id: u64, index: u64, value_bytes: &[u8]| {
            iter::empty()
                .chain(tx_id.to_be_bytes()) // tx_id
                .chain(index.to_be_bytes()) // index
                .chain(value_bytes.to_vec()) // value
        };
        let tx_bytes_fn = |tx_id: u64, index: u64, tx: &TxValues| {
            vec![
                tx.nonce.to_be_bytes().to_vec(),                     // nonce
                tx.gas_limit.to_be_bytes().to_vec(),                 // gas_limit
                tx.gas_price.to_be_bytes().to_vec(),                 // gas price
                tx.from_addr.as_fixed_bytes().to_vec(),              // from_addr
                tx.to_addr.as_fixed_bytes().to_vec(),                // to_addr
                tx.is_create.to_be_bytes().to_vec(),                 // is_create
                tx.value.to_be_bytes().to_vec(),                     // value
                tx.call_data_len.to_be_bytes().to_vec(),             // call_data_len
                tx.call_data_gas_cost.to_be_bytes().to_vec(),        // call_data_gas_cost
                tx.tx_sign_hash.iter().rev().copied().collect_vec(), // tx sign hash
            ]
            .iter()
            .flat_map(move |value_bytes| tx_field_byte_fn(tx_id, index, value_bytes))
            .collect_vec()
        };

        let txs_values = self.get_tx_table_values();
        let tx_values_default = TxValues::default();

        // all tx bytes including tx padding
        let all_tx_bytes = iter::empty()
            .chain(&txs_values)
            .chain((0..(max_txs - txs_values.len())).map(|_| &tx_values_default))
            .enumerate()
            .flat_map(|(i, tx)| {
                let i: u64 = i.try_into().unwrap();
                tx_bytes_fn(i + 1, 0, tx)
            });

        // first tx empty row happened here
        let result = result
            .chain(tx_field_byte_fn(0, 0, &[0u8; 1])) // empty row
            .chain(all_tx_bytes);

        // Tx Table CallData
        let all_calldata = self
            .transactions
            .iter()
            .flat_map(|tx| tx.call_data.0.as_ref().iter().copied())
            .collect_vec();
        let calldata_count = all_calldata.len();
        // concat call data with call data padding
        let calldata_chain = iter::empty()
            .chain(all_calldata)
            .chain((0..max_calldata - calldata_count).map(|_| 0u8));
        result.chain(calldata_chain).collect_vec()
    }

    /// generate public data from validator perspective
    pub fn get_rpi_digest_word<F: Field>(
        &self,
        max_txs: usize,
        max_calldata: usize,
    ) -> word::Word<F> {
        let mut keccak = Keccak::default();
        keccak.update(&self.get_pi_bytes(max_txs, max_calldata));
        let digest = keccak.digest();
        word::Word::from(Word::from_big_endian(&digest))
    }
}

/// convert witness block to public data
pub fn public_data_convert<F: Field>(block: &Block<F>) -> PublicData {
    PublicData {
        chain_id: block.context.chain_id,
        history_hashes: block.context.history_hashes.clone(),
        transactions: block.txs.iter().map(|tx| tx.deref().clone()).collect_vec(),
        state_root: block.eth_block.state_root,
        prev_state_root: H256::from_uint(&block.prev_state_root),
        block_hash: block.eth_block.hash,
        block_constants: BlockConstants {
            coinbase: block.context.coinbase,
            timestamp: block.context.timestamp,
            number: block.context.number.as_u64().into(),
            difficulty: block.context.difficulty,
            gas_limit: block.context.gas_limit.into(),
            base_fee: block.context.base_fee,
        },
    }
}
