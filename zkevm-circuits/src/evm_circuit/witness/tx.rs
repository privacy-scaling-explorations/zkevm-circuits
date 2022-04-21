use digest::Digest;
use eth_types::{Address, ToLittleEndian, Word, U256};
use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};
use num::Zero;
use sha3::Keccak256;

use crate::{
    evm_circuit::{
        util::RandomLinearCombination,
        witness::{
            rlp_witness::{RlpDataType, RlpWitnessGen, RlpWitnessRow},
            Transaction,
        },
    },
    impl_expr,
};

/// Tags used to tag rows in the RLP circuit for a transaction.
#[derive(Clone, Copy, Debug)]
pub enum RlpTxTag {
    /// Denotes the prefix bytes indicating the “length of length” and/or
    /// “length” of the tx’s RLP-encoding.
    Prefix = 1,
    /// Denotes the byte(s) for the tx’s nonce.
    Nonce,
    /// Denotes the byte(s) for the tx’s gas price.
    GasPrice,
    /// Denotes the byte(s) for the tx’s gas.
    Gas,
    /// Denotes the prefix byte indicating the “length” of the tx’s to.
    ToPrefix,
    /// Denotes the bytes for the tx’s to.
    To,
    /// Denotes the byte(s) for the tx’s value.
    Value,
    /// Denotes the prefix byte(s) indicating the “length of length” and/or
    /// “length” of the tx’s data.
    DataPrefix,
    /// Denotes the bytes for the tx’s data.
    Data,
}

impl_expr!(RlpTxTag);

/// Denotes the number of possible tag values for a tx row.
pub const N_TX_TAGS: usize = 9;

impl<F: FieldExt> RlpWitnessGen<F> for Transaction {
    fn gen_witness(&self, randomness: F) -> Vec<RlpWitnessRow<F>> {
        let rlp_data = rlp::encode(self);
        let hash = Word::from_big_endian(Keccak256::digest(&rlp_data).as_slice());
        let hash = RandomLinearCombination::random_linear_combine(hash.to_le_bytes(), randomness);

        let mut rows = Vec::with_capacity(rlp_data.len());

        let idx = handle_prefix(rlp_data.as_ref(), hash, &mut rows, 0);
        let idx = handle_u256(
            rlp_data.as_ref(),
            hash,
            &mut rows,
            RlpTxTag::Nonce,
            self.nonce.into(),
            idx,
        );
        let idx = handle_u256(
            rlp_data.as_ref(),
            hash,
            &mut rows,
            RlpTxTag::GasPrice,
            self.gas_price,
            idx,
        );
        let idx = handle_u256(
            rlp_data.as_ref(),
            hash,
            &mut rows,
            RlpTxTag::Gas,
            self.gas.into(),
            idx,
        );
        let idx = handle_address(rlp_data.as_ref(), hash, &mut rows, self.callee_address, idx);
        let idx = handle_u256(
            rlp_data.as_ref(),
            hash,
            &mut rows,
            RlpTxTag::Value,
            self.value,
            idx,
        );
        let idx = handle_bytes(rlp_data.as_ref(), hash, &mut rows, &self.call_data, idx);

        assert!(
            idx == rlp_data.len(),
            "RLP data mismatch: idx != len(rlp_data)"
        );
        rows
    }
}

fn handle_prefix<F: FieldExt>(
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    mut idx: usize,
) -> usize {
    if rlp_data[idx] > 247 {
        // length of length
        let length_of_length = (rlp_data[idx] - 247) as usize;
        let tag_length = length_of_length + 1;
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: rlp_data[idx],
            tag: RlpTxTag::Prefix as u8,
            tag_length,
            tag_index: tag_length,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: 0,
            hash,
        });
        idx += 1;
        let mut length_acc = 0;
        for (k, rlp_byte) in rlp_data.iter().skip(idx).take(length_of_length).enumerate() {
            length_acc = (length_acc * 256) + (*rlp_byte as u64);
            rows.push(RlpWitnessRow {
                index: idx + 1,
                data_type: RlpDataType::Transaction,
                value: *rlp_byte,
                tag: RlpTxTag::Prefix as u8,
                tag_length,
                tag_index: tag_length - (1 + k),
                aux_tag_index: 0,
                aux_tag_length: 0,
                length_acc,
                hash,
            });
            idx += 1;
        }
    } else {
        // length
        assert!(
            rlp_data[idx] > 191 && rlp_data[idx] < 248,
            "RLP data mismatch({:?}): 191 < value < 248",
            RlpTxTag::Prefix,
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: rlp_data[idx],
            tag: RlpTxTag::Prefix as u8,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: (rlp_data[idx] - 192) as u64,
            hash,
        });
        idx += 1;
    }
    idx
}

fn handle_u256<F: FieldExt>(
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    tag: RlpTxTag,
    value: U256,
    mut idx: usize,
) -> usize {
    let mut value_bytes = vec![0u8; 32];
    value.to_big_endian(&mut value_bytes);
    let value_bytes = value_bytes
        .iter()
        .skip_while(|b| b.is_zero())
        .cloned()
        .collect::<Vec<u8>>();

    if value_bytes.is_empty() {
        assert!(
            rlp_data[idx] == 128,
            "RLP data mismatch({:?}): value == 128",
            tag,
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: 128,
            tag: tag as u8,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: 0,
            hash,
        });
        idx += 1;
    } else if value_bytes.len() == 1 && value_bytes[0] < 128 {
        assert!(
            rlp_data[idx] == value_bytes[0],
            "RLP data mismatch({:?}): value < 128",
            tag,
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: value_bytes[0],
            tag: tag as u8,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: 0,
            hash,
        });
        idx += 1;
    } else {
        assert!(
            rlp_data[idx] as usize == 128 + value_bytes.len(),
            "RLP data mismatch({:?}): len(value)",
            tag,
        );
        let tag_length = 1 + value_bytes.len();
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: rlp_data[idx],
            tag: tag as u8,
            tag_length,
            aux_tag_index: 0,
            aux_tag_length: 0,
            tag_index: tag_length,
            length_acc: value_bytes.len() as u64,
            hash,
        });
        idx += 1;

        for (i, value_byte) in value_bytes.iter().enumerate() {
            assert!(
                rlp_data[idx] == *value_byte,
                "RLP data mismatch({:?}): value[{}]",
                tag,
                i,
            );
            rows.push(RlpWitnessRow {
                index: idx + 1,
                data_type: RlpDataType::Transaction,
                value: *value_byte,
                tag: tag as u8,
                tag_length,
                tag_index: tag_length - (1 + i),
                aux_tag_index: 0,
                aux_tag_length: 0,
                length_acc: 0,
                hash,
            });
            idx += 1;
        }
    }

    idx
}

fn handle_address<F: FieldExt>(
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    value: Address,
    mut idx: usize,
) -> usize {
    let value_bytes = value.as_fixed_bytes();

    assert!(
        rlp_data[idx] == 148,
        "RLP data mismatch({:?}): value",
        RlpTxTag::ToPrefix,
    );
    rows.push(RlpWitnessRow {
        index: idx + 1,
        data_type: RlpDataType::Transaction,
        value: 148,
        tag: RlpTxTag::ToPrefix as u8,
        tag_length: 1,
        tag_index: 1,
        aux_tag_index: 0,
        aux_tag_length: 0,
        length_acc: 20,
        hash,
    });
    idx += 1;

    for (i, value_byte) in value_bytes.iter().enumerate() {
        assert!(
            rlp_data[idx] == *value_byte,
            "RLP data mismatch({:?}): value[{}]",
            RlpTxTag::To,
            i,
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: *value_byte,
            tag: RlpTxTag::To as u8,
            tag_length: 20,
            tag_index: 20 - i,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: 0,
            hash,
        });
        idx += 1;
    }

    idx
}

fn handle_bytes<F: FieldExt>(
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    call_data: &[u8],
    mut idx: usize,
) -> usize {
    let length = call_data.len();

    if length == 0 {
        assert!(
            rlp_data[idx] == 128,
            "RLP data mismatch({:?}): len(call_data) == 0",
            RlpTxTag::DataPrefix
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: 128,
            tag: RlpTxTag::DataPrefix as u8,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: 0,
            hash,
        });
        idx += 1;
        return idx;
    }

    if length < 56 {
        assert!(
            rlp_data[idx] as usize == 128 + length,
            "RLP data mismatch({:?}): len(call_data) + 128",
            RlpTxTag::DataPrefix,
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: (128 + length) as u8,
            tag: RlpTxTag::DataPrefix as u8,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: length as u64,
            hash,
        });
        idx += 1;

        for (i, data_byte) in call_data.iter().enumerate() {
            assert!(
                rlp_data[idx] == *data_byte,
                "RLP data mismatch({:?}): value[{}]",
                RlpTxTag::Data,
                i,
            );
            rows.push(RlpWitnessRow {
                index: idx + 1,
                data_type: RlpDataType::Transaction,
                value: *data_byte,
                tag: RlpTxTag::Data as u8,
                tag_length: length,
                tag_index: length - i,
                aux_tag_index: 0,
                aux_tag_length: 0,
                length_acc: 0,
                hash,
            });
            idx += 1;
        }
        return idx;
    }

    // length > 55.
    let length_of_length = 8 - length.leading_zeros() as usize / 8;
    assert!(
        rlp_data[idx] as usize == 183 + length_of_length,
        "RLP data mismatch({:?}): len_of_len(call_data) + 183",
        RlpTxTag::DataPrefix,
    );
    let tag_length = 1 + length_of_length;
    rows.push(RlpWitnessRow {
        index: idx + 1,
        data_type: RlpDataType::Transaction,
        value: (183 + length_of_length) as u8,
        tag: RlpTxTag::DataPrefix as u8,
        tag_length,
        tag_index: tag_length,
        aux_tag_index: 0,
        aux_tag_length: 0,
        length_acc: 0,
        hash,
    });
    idx += 1;

    let length_bytes = length.to_be_bytes();
    let length_bytes = length_bytes
        .iter()
        .skip_while(|b| b.is_zero())
        .cloned()
        .collect::<Vec<u8>>();
    let mut length_acc = 0;
    for (i, length_byte) in length_bytes.iter().enumerate() {
        assert!(
            rlp_data[idx] == *length_byte,
            "RLP data mismatch({:?}): length[{}]",
            RlpTxTag::DataPrefix,
            i,
        );
        length_acc = length_acc * 256 + (*length_byte as u64);
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: *length_byte,
            tag: RlpTxTag::DataPrefix as u8,
            tag_length,
            tag_index: tag_length - (1 + i),
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc,
            hash,
        });
        idx += 1;
    }

    let tag_length = call_data.len();
    for (i, data_byte) in call_data.iter().enumerate() {
        assert!(
            rlp_data[idx] == *data_byte,
            "RLP data mismatch({:?}): data[{}]",
            RlpTxTag::Data,
            i,
        );
        rows.push(RlpWitnessRow {
            index: idx + 1,
            data_type: RlpDataType::Transaction,
            value: *data_byte,
            tag: RlpTxTag::Data as u8,
            tag_length,
            tag_index: tag_length - i,
            aux_tag_index: 0,
            aux_tag_length: 0,
            length_acc: 0,
            hash,
        });
        idx += 1;
    }
    idx
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use num::Zero;
    use pairing::bn256::Fr;

    use crate::evm_circuit::{
        test::rand_bytes,
        witness::{rlp_witness::RlpWitnessGen, tx::RlpTxTag, Transaction},
    };

    #[test]
    fn tx_rlp_witgen_a() {
        let r = Fr::random(rand::thread_rng());

        let callee_address = mock::MOCK_ACCOUNTS[0];
        let call_data = rand_bytes(55);
        let tx = Transaction {
            nonce: 1,
            gas_price: 2u64.into(),
            gas: 3,
            callee_address,
            value: 4u64.into(),
            call_data: call_data.clone(),
            ..Default::default()
        };

        let tx_rlp = rlp::encode(&tx);
        let witness_rows = tx.gen_witness(r);

        assert_eq!(tx_rlp.len(), witness_rows.len());

        // prefix verification
        assert_eq!(witness_rows[0].tag, RlpTxTag::Prefix as u8);
        assert_eq!(witness_rows[0].tag_index, 2);
        assert_eq!(witness_rows[0].tag_length, 2);
        assert_eq!(witness_rows[0].length_acc, 0);
        assert_eq!(witness_rows[0].value, 248);
        assert_eq!(witness_rows[1].tag, RlpTxTag::Prefix as u8);
        assert_eq!(witness_rows[1].tag_index, 1);
        assert_eq!(witness_rows[1].tag_length, 2);
        assert_eq!(witness_rows[1].length_acc, 81);
        assert_eq!(witness_rows[1].value, 81);

        // nonce verification
        assert_eq!(witness_rows[2].tag, RlpTxTag::Nonce as u8);
        assert_eq!(witness_rows[2].tag_index, 1);
        assert_eq!(witness_rows[2].tag_length, 1);
        assert_eq!(witness_rows[2].value, 1);

        // gas price verification
        assert_eq!(witness_rows[3].tag, RlpTxTag::GasPrice as u8);
        assert_eq!(witness_rows[3].tag_index, 1);
        assert_eq!(witness_rows[3].tag_length, 1);
        assert_eq!(witness_rows[3].value, 2);

        // gas verification
        assert_eq!(witness_rows[4].tag, RlpTxTag::Gas as u8);
        assert_eq!(witness_rows[4].tag_index, 1);
        assert_eq!(witness_rows[4].tag_length, 1);
        assert_eq!(witness_rows[4].value, 3);

        // to prefix verification
        assert_eq!(witness_rows[5].tag, RlpTxTag::ToPrefix as u8);
        assert_eq!(witness_rows[5].tag_index, 1);
        assert_eq!(witness_rows[5].tag_length, 1);
        assert_eq!(witness_rows[5].value, 148);

        // to verification
        for (i, row) in witness_rows.iter().skip(6).take(20).enumerate() {
            assert_eq!(row.tag, RlpTxTag::To as u8);
            assert_eq!(row.tag_index, 20 - i);
            assert_eq!(row.tag_length, 20);
            assert_eq!(row.value, mock::MOCK_ACCOUNTS[0][i]);
        }

        // value verification
        assert_eq!(witness_rows[26].tag, RlpTxTag::Value as u8);
        assert_eq!(witness_rows[26].tag_index, 1);
        assert_eq!(witness_rows[26].tag_length, 1);
        assert_eq!(witness_rows[26].value, 4);

        // data prefix verification
        assert_eq!(witness_rows[27].tag, RlpTxTag::DataPrefix as u8);
        assert_eq!(witness_rows[27].tag_index, 1);
        assert_eq!(witness_rows[27].tag_length, 1);
        assert_eq!(witness_rows[27].value, 128 + 55);
        assert_eq!(witness_rows[27].length_acc, 55);

        // data verification
        for (i, row) in witness_rows.iter().skip(28).take(55).enumerate() {
            assert_eq!(row.tag, RlpTxTag::Data as u8);
            assert_eq!(row.tag_index, 55 - i);
            assert_eq!(row.tag_length, 55);
            assert_eq!(row.value, call_data[i]);
        }
    }

    #[test]
    fn tx_rlp_witgen_b() {
        let r = Fr::random(rand::thread_rng());

        let nonce = 0x123456u64;
        let gas_price = 0x234567u64.into();
        let gas = 0x345678u64;
        let callee_address = mock::MOCK_ACCOUNTS[1];
        let value = 0x456789u64.into();
        let call_data = rand_bytes(2048);
        let tx = Transaction {
            nonce,
            gas_price,
            gas,
            callee_address,
            value,
            call_data: call_data.clone(),
            ..Default::default()
        };

        let tx_rlp = rlp::encode(&tx);
        let witness_rows = tx.gen_witness(r);

        assert_eq!(tx_rlp.len(), witness_rows.len());

        // prefix verification
        assert_eq!(witness_rows[0].tag, RlpTxTag::Prefix as u8);
        assert_eq!(witness_rows[0].tag_index, 3);
        assert_eq!(witness_rows[0].tag_length, 3);
        assert_eq!(witness_rows[0].length_acc, 0);
        assert_eq!(witness_rows[0].value, 249);
        assert_eq!(witness_rows[1].tag, RlpTxTag::Prefix as u8);
        assert_eq!(witness_rows[1].tag_index, 2);
        assert_eq!(witness_rows[1].tag_length, 3);
        assert_eq!(witness_rows[1].length_acc, 8);
        assert_eq!(witness_rows[1].value, 8);
        assert_eq!(witness_rows[2].tag, RlpTxTag::Prefix as u8);
        assert_eq!(witness_rows[2].tag_index, 1);
        assert_eq!(witness_rows[2].tag_length, 3);
        assert_eq!(witness_rows[2].length_acc, 2088);
        assert_eq!(witness_rows[2].value, 40);

        // nonce verification
        let nonce_bytes = nonce
            .to_be_bytes()
            .iter()
            .skip_while(|b| b.is_zero())
            .cloned()
            .collect::<Vec<u8>>();
        assert_eq!(nonce_bytes.len(), 3);
        assert_eq!(witness_rows[3].tag, RlpTxTag::Nonce as u8);
        assert_eq!(witness_rows[3].tag_length, 4);
        assert_eq!(witness_rows[3].tag_index, 4);
        assert_eq!(witness_rows[3].value, 128 + 3);
        assert_eq!(witness_rows[3].length_acc, 3);
        for (i, row) in witness_rows.iter().skip(4).take(3).enumerate() {
            assert_eq!(row.tag, RlpTxTag::Nonce as u8);
            assert_eq!(row.tag_length, 4);
            assert_eq!(row.tag_index, 3 - i);
            assert_eq!(row.value, nonce_bytes[i]);
            assert_eq!(row.length_acc, 0);
        }

        const START_DATA_PREFIX: usize = 3 + // prefix
            4 +  // nonce
            4 +  // gas price
            4 +  // gas
            21 + // callee address
            4; // value
        assert_eq!(
            witness_rows[START_DATA_PREFIX - 1].tag,
            RlpTxTag::Value as u8
        );

        // data prefix verification
        // 2048 -> 0x0800 -> len_of_len == 2
        assert_eq!(
            witness_rows[START_DATA_PREFIX].tag,
            RlpTxTag::DataPrefix as u8
        );
        assert_eq!(witness_rows[START_DATA_PREFIX].tag_index, 3);
        assert_eq!(witness_rows[START_DATA_PREFIX].tag_length, 3);
        assert_eq!(witness_rows[START_DATA_PREFIX].value, 183 + 2);
        assert_eq!(witness_rows[START_DATA_PREFIX].length_acc, 0);
        assert_eq!(
            witness_rows[START_DATA_PREFIX + 1].tag,
            RlpTxTag::DataPrefix as u8
        );
        assert_eq!(witness_rows[START_DATA_PREFIX + 1].tag_index, 2);
        assert_eq!(witness_rows[START_DATA_PREFIX + 1].tag_length, 3);
        assert_eq!(witness_rows[START_DATA_PREFIX + 1].value, 8);
        assert_eq!(witness_rows[START_DATA_PREFIX + 1].length_acc, 8);
        assert_eq!(
            witness_rows[START_DATA_PREFIX + 2].tag,
            RlpTxTag::DataPrefix as u8
        );
        assert_eq!(witness_rows[START_DATA_PREFIX + 2].tag_index, 1);
        assert_eq!(witness_rows[START_DATA_PREFIX + 2].tag_length, 3);
        assert_eq!(witness_rows[START_DATA_PREFIX + 2].value, 0);
        assert_eq!(witness_rows[START_DATA_PREFIX + 2].length_acc, 2048);

        // data verification
        assert_eq!(
            witness_rows[START_DATA_PREFIX + 3].tag,
            RlpTxTag::Data as u8
        );
        assert_eq!(witness_rows[START_DATA_PREFIX + 3].tag_index, 2048);
        assert_eq!(witness_rows[START_DATA_PREFIX + 3].tag_length, 2048);
        assert_eq!(witness_rows[START_DATA_PREFIX + 3].value, call_data[0]);
        assert_eq!(witness_rows[START_DATA_PREFIX + 3].length_acc, 0);
    }
}
