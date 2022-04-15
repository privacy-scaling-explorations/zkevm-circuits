use eth_types::{Address, U256};
use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};
use num::Zero;

use crate::impl_expr;

use super::{
    rlp_witness::{RlpDataType, RlpWitnessGen, RlpWitnessRow},
    Transaction,
};

/// Tags used to tag rows in the RLP circuit for a transaction.
#[derive(Clone, Copy, Debug)]
pub enum RlpTxTag {
    /// Denotes the prefix bytes indicating the “length of length” and/or
    /// “length” of the tx’s RLP-encoding.
    Prefix,
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
    fn gen_witness(&self) -> Vec<RlpWitnessRow> {
        let rlp_data = rlp::encode(self);

        let mut rows = Vec::with_capacity(rlp_data.len());

        let idx = handle_prefix(rlp_data.as_ref(), &mut rows, 0);
        let idx = handle_u256(
            rlp_data.as_ref(),
            &mut rows,
            RlpTxTag::Nonce,
            self.nonce.into(),
            idx,
        );
        let idx = handle_u256(
            rlp_data.as_ref(),
            &mut rows,
            RlpTxTag::GasPrice,
            self.gas_price,
            idx,
        );
        let idx = handle_u256(
            rlp_data.as_ref(),
            &mut rows,
            RlpTxTag::Gas,
            self.gas.into(),
            idx,
        );
        let idx = handle_address(rlp_data.as_ref(), &mut rows, self.callee_address, idx);
        let idx = handle_u256(
            rlp_data.as_ref(),
            &mut rows,
            RlpTxTag::Value,
            self.value,
            idx,
        );
        let idx = handle_bytes(rlp_data.as_ref(), &mut rows, &self.call_data, idx);

        assert!(
            idx == rlp_data.len(),
            "RLP data mismatch: idx != len(rlp_data)"
        );
        rows
    }
}

fn handle_prefix(rlp_data: &[u8], rows: &mut Vec<RlpWitnessRow>, mut idx: usize) -> usize {
    if rlp_data[idx] > 183 && rlp_data[idx] < 192 {
        // length of length
        let length_of_length = (rlp_data[idx] - 183) as usize;
        let tag_length = length_of_length + 1;
        rows.push(RlpWitnessRow {
            index: idx,
            data_type: RlpDataType::Transaction,
            value: rlp_data[idx],
            tag: RlpTxTag::Prefix as u8,
            tag_length,
            tag_index: tag_length,
            length_acc: 0,
        });
        idx += 1;
        let mut length_acc = 0;
        for (k, rlp_byte) in rlp_data.iter().skip(idx).take(length_of_length).enumerate() {
            length_acc = (length_acc * 256) + (*rlp_byte as u64);
            rows.push(RlpWitnessRow {
                index: idx + k,
                data_type: RlpDataType::Transaction,
                value: *rlp_byte,
                tag: RlpTxTag::Prefix as u8,
                tag_length,
                tag_index: tag_length - (idx + k),
                length_acc,
            });
            idx += 1;
        }
    } else {
        // length
        assert!(
            rlp_data[idx] > 127 && rlp_data[idx] < 184,
            "RLP data mismatch({:?}): 127 < value < 184",
            RlpTxTag::Prefix,
        );
        rows.push(RlpWitnessRow {
            index: idx,
            data_type: RlpDataType::Transaction,
            value: rlp_data[idx],
            tag: RlpTxTag::Prefix as u8,
            tag_length: 1,
            tag_index: 1,
            length_acc: (rlp_data[idx] - 127) as u64,
        });
        idx += 1;
    }
    idx
}

fn handle_u256(
    rlp_data: &[u8],
    rows: &mut Vec<RlpWitnessRow>,
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
            rlp_data[idx] == 0,
            "RLP data mismatch({:?}): value == 0",
            tag,
        );
        rows.push(RlpWitnessRow {
            index: idx,
            data_type: RlpDataType::Transaction,
            value: 0,
            tag: tag as u8,
            tag_length: 1,
            tag_index: 1,
            length_acc: 0,
        });
        idx += 1;
    } else if value_bytes.len() == 1 && value_bytes[0] < 128 {
        assert!(
            rlp_data[idx] == value_bytes[0],
            "RLP data mismatch({:?}): value < 128",
            tag,
        );
        rows.push(RlpWitnessRow {
            index: idx,
            data_type: RlpDataType::Transaction,
            value: value_bytes[0],
            tag: tag as u8,
            tag_length: 1,
            tag_index: 1,
            length_acc: 0,
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
            index: idx,
            data_type: RlpDataType::Transaction,
            value: rlp_data[idx],
            tag: tag as u8,
            tag_length,
            tag_index: tag_length,
            length_acc: 1,
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
                index: idx,
                data_type: RlpDataType::Transaction,
                value: *value_byte,
                tag: tag as u8,
                tag_length,
                tag_index: tag_length - (1 + i),
                length_acc: 0,
            });
            idx += 1;
        }
    }

    idx
}

fn handle_address(
    rlp_data: &[u8],
    rows: &mut Vec<RlpWitnessRow>,
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
        index: idx,
        data_type: RlpDataType::Transaction,
        value: 148,
        tag: RlpTxTag::ToPrefix as u8,
        tag_length: 1,
        tag_index: 1,
        length_acc: 20,
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
            index: idx,
            data_type: RlpDataType::Transaction,
            value: *value_byte,
            tag: RlpTxTag::To as u8,
            tag_length: 20,
            tag_index: 20 - i,
            length_acc: 0,
        });
        idx += 1;
    }

    idx
}

fn handle_bytes(
    rlp_data: &[u8],
    rows: &mut Vec<RlpWitnessRow>,
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
            index: idx,
            data_type: RlpDataType::Transaction,
            value: 128,
            tag: RlpTxTag::DataPrefix as u8,
            tag_length: 1,
            tag_index: 1,
            length_acc: 0,
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
            index: idx,
            data_type: RlpDataType::Transaction,
            value: (128 + length) as u8,
            tag: RlpTxTag::DataPrefix as u8,
            tag_length: 1,
            tag_index: 1,
            length_acc: length as u64,
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
                index: idx,
                data_type: RlpDataType::Transaction,
                value: *data_byte,
                tag: RlpTxTag::Data as u8,
                tag_length: length,
                tag_index: length - i,
                length_acc: 0,
            });
            idx += 1;
        }
        return idx;
    }

    // length > 55.
    let length_of_length = 1 + 8 - length.leading_zeros() as usize / 8;
    assert!(
        rlp_data[idx] as usize == 183 + length_of_length,
        "RLP data mismatch({:?}): len_of_len(call_data) + 183",
        RlpTxTag::DataPrefix,
    );
    let tag_length = 1 + length_of_length;
    rows.push(RlpWitnessRow {
        index: idx,
        data_type: RlpDataType::Transaction,
        value: (183 + length_of_length) as u8,
        tag: RlpTxTag::DataPrefix as u8,
        tag_length,
        tag_index: tag_length,
        length_acc: 0,
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
            index: idx,
            data_type: RlpDataType::Transaction,
            value: *length_byte,
            tag: RlpTxTag::DataPrefix as u8,
            tag_length,
            tag_index: tag_length - (1 + i),
            length_acc,
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
            index: idx,
            data_type: RlpDataType::Transaction,
            value: *data_byte,
            tag: RlpTxTag::Data as u8,
            tag_length,
            tag_index: tag_length - (1 + i),
            length_acc: 0,
        });
        idx += 1;
    }
    idx
}
