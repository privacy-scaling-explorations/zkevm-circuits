use eth_types::{Address, U256};
use halo2_proofs::arithmetic::FieldExt;
use num::Zero;

use crate::witness::RlpTxTag;

use super::witness_gen::{RlpDataType, RlpWitnessRow};

pub fn handle_prefix<F: FieldExt>(
    id: usize,
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    data_type: RlpDataType,
    tag: u8,
    mut idx: usize,
) -> usize {
    if rlp_data[idx] > 247 {
        // length of length
        let length_of_length = (rlp_data[idx] - 247) as usize;
        let tag_length = length_of_length + 1;
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: rlp_data[idx],
            value_acc: F::from(rlp_data[idx] as u64),
            tag,
            tag_length,
            tag_index: tag_length,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc: 0,
            hash,
        });
        idx += 1;
        let mut length_acc = 0;
        for (k, rlp_byte) in rlp_data.iter().skip(idx).take(length_of_length).enumerate() {
            length_acc = (length_acc * 256) + (*rlp_byte as u64);
            rows.push(RlpWitnessRow {
                id,
                index: idx + 1,
                data_type,
                value: *rlp_byte,
                value_acc: F::from(length_acc as u64),
                tag,
                tag_length,
                tag_index: tag_length - (1 + k),
                aux_tag_index: [0; 2],
                aux_tag_length: [0; 2],
                length_acc,
                hash,
            });
            idx += 1;
        }
    } else {
        // length
        assert!(
            rlp_data[idx] > 191 && rlp_data[idx] < 248,
            "RLP data mismatch({:?}): 191 < value < 248, got: {:?} at idx: {:?}",
            tag,
            rlp_data[idx],
            idx,
        );
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: rlp_data[idx],
            value_acc: F::from(rlp_data[idx] as u64),
            tag,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc: (rlp_data[idx] - 192) as u64,
            hash,
        });
        idx += 1;
    }
    idx
}

#[allow(clippy::too_many_arguments)]
pub fn handle_u256<F: FieldExt>(
    randomness: F,
    id: usize,
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    data_type: RlpDataType,
    tag: u8,
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
            id,
            index: idx + 1,
            data_type,
            value: 128,
            value_acc: F::from(128),
            tag,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
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
            id,
            index: idx + 1,
            data_type,
            value: value_bytes[0],
            value_acc: F::from(value_bytes[0] as u64),
            tag,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
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
            id,
            index: idx + 1,
            data_type,
            value: rlp_data[idx],
            value_acc: F::from(rlp_data[idx] as u64),
            tag,
            tag_length,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            tag_index: tag_length,
            length_acc: value_bytes.len() as u64,
            hash,
        });
        idx += 1;

        let mut value_acc = F::zero();
        for (i, value_byte) in value_bytes.iter().enumerate() {
            assert!(
                rlp_data[idx] == *value_byte,
                "RLP data mismatch({:?}): value[{}]",
                tag,
                i,
            );
            if data_type == RlpDataType::Transaction {
                if tag == RlpTxTag::Value as u8 || tag == RlpTxTag::GasPrice as u8 {
                    value_acc = value_acc * randomness + F::from(*value_byte as u64);
                } else {
                    value_acc = value_acc * F::from(256) + F::from(*value_byte as u64);
                }
            }
            rows.push(RlpWitnessRow {
                id,
                index: idx + 1,
                data_type,
                value: *value_byte,
                value_acc,
                tag,
                tag_length,
                tag_index: tag_length - (1 + i),
                aux_tag_index: [0; 2],
                aux_tag_length: [0; 2],
                length_acc: 0,
                hash,
            });
            idx += 1;
        }
    }

    idx
}

#[allow(clippy::too_many_arguments)]
pub fn handle_address<F: FieldExt>(
    id: usize,
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    data_type: RlpDataType,
    prefix_tag: u8,
    tag: u8,
    value: Address,
    mut idx: usize,
) -> usize {
    let value_bytes = value.as_fixed_bytes();

    assert!(
        rlp_data[idx] == 148,
        "RLP data mismatch({:?}): value",
        prefix_tag,
    );
    rows.push(RlpWitnessRow {
        id,
        index: idx + 1,
        data_type,
        value: 148,
        value_acc: F::from(148),
        tag: prefix_tag,
        tag_length: 1,
        tag_index: 1,
        aux_tag_index: [0; 2],
        aux_tag_length: [0; 2],
        length_acc: 20,
        hash,
    });
    idx += 1;

    let mut value_acc = F::zero();
    for (i, value_byte) in value_bytes.iter().enumerate() {
        assert!(
            rlp_data[idx] == *value_byte,
            "RLP data mismatch({:?}): value[{}]",
            tag,
            i,
        );
        value_acc = value_acc * F::from(256) + F::from(*value_byte as u64);
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: *value_byte,
            value_acc,
            tag,
            tag_length: 20,
            tag_index: 20 - i,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc: 0,
            hash,
        });
        idx += 1;
    }

    idx
}

#[allow(clippy::too_many_arguments)]
pub fn handle_bytes<F: FieldExt>(
    randomness: F,
    id: usize,
    rlp_data: &[u8],
    hash: F,
    rows: &mut Vec<RlpWitnessRow<F>>,
    data_type: RlpDataType,
    prefix_tag: u8,
    tag: u8,
    call_data: &[u8],
    mut idx: usize,
) -> usize {
    let length = call_data.len();

    if length == 0 {
        assert!(
            rlp_data[idx] == 128,
            "RLP data mismatch({:?}): len(call_data) == 0",
            prefix_tag,
        );
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: 128,
            value_acc: F::from(128),
            tag: prefix_tag,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
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
            prefix_tag,
        );
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: (128 + length) as u8,
            value_acc: F::from((128 + length) as u64),
            tag: prefix_tag,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc: length as u64,
            hash,
        });
        idx += 1;

        for (i, data_byte) in call_data.iter().enumerate() {
            assert!(
                rlp_data[idx] == *data_byte,
                "RLP data mismatch({:?}): value[{}]",
                tag,
                i,
            );
            rows.push(RlpWitnessRow {
                id,
                index: idx + 1,
                data_type,
                value: *data_byte,
                value_acc: F::from(*data_byte as u64),
                tag,
                tag_length: length,
                tag_index: length - i,
                aux_tag_index: [0; 2],
                aux_tag_length: [0; 2],
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
        prefix_tag,
    );
    let tag_length = 1 + length_of_length;
    rows.push(RlpWitnessRow {
        id,
        index: idx + 1,
        data_type,
        value: (183 + length_of_length) as u8,
        value_acc: F::from((183 + length_of_length) as u64),
        tag: prefix_tag,
        tag_length,
        tag_index: tag_length,
        aux_tag_index: [0; 2],
        aux_tag_length: [0; 2],
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
            prefix_tag,
            i,
        );
        length_acc = length_acc * 256 + (*length_byte as u64);
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: *length_byte,
            value_acc: F::from(length_acc as u64),
            tag: prefix_tag,
            tag_length,
            tag_index: tag_length - (1 + i),
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc,
            hash,
        });
        idx += 1;
    }

    let tag_length = call_data.len();
    let mut value_acc = F::zero();
    for (i, data_byte) in call_data.iter().enumerate() {
        assert!(
            rlp_data[idx] == *data_byte,
            "RLP data mismatch({:?}): data[{}]",
            tag,
            i,
        );
        value_acc = value_acc * randomness + F::from(*data_byte as u64);
        rows.push(RlpWitnessRow {
            id,
            index: idx + 1,
            data_type,
            value: *data_byte,
            value_acc,
            tag,
            tag_length,
            tag_index: tag_length - i,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc: 0,
            hash,
        });
        idx += 1;
    }
    idx
}
