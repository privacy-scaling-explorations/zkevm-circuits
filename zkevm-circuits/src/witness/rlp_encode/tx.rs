use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

use crate::{evm_circuit::witness::Transaction, impl_expr};

use super::{
    common::{handle_address, handle_bytes, handle_prefix, handle_u256},
    witness_gen::{RlpDataType, RlpWitnessGen, RlpWitnessRow},
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
    /// Denotes the chain ID, as per EIP-155.
    ChainId,
    /// Denotes a placeholder zero for unsigned transactions, as per EIP-155.
    Zero,
    /// Used to indicate the {0, 1}-parity of the ECDSA signature.
    SigV,
    /// ECDSA signature's X-coordinate.
    SigR,
    /// ECDSA signature's Y-coordinate.
    SigS,
    /// The RLP tag is reserved to hold the RLP-encoding's random linear
    /// combination in its accumulator value. Its used to support a lookup
    /// for rlc(rlp(tx)).
    Rlp,
}

impl_expr!(RlpTxTag);

/// Denotes the number of tag values in a transaction's RLP trace.
pub const N_TX_TAGS: usize = 13;

impl<F: FieldExt> RlpWitnessGen<F> for Transaction {
    fn gen_witness(&self, randomness: F) -> Vec<RlpWitnessRow<F>> {
        let rlp_data = rlp::encode(self);
        let mut rows = Vec::with_capacity(rlp_data.len());

        let idx = handle_prefix(
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::Prefix as u8,
            0,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::Nonce as u8,
            self.nonce.into(),
            idx,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::GasPrice as u8,
            self.gas_price,
            idx,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::Gas as u8,
            self.gas.into(),
            idx,
        );
        let idx = handle_address(
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::ToPrefix as u8,
            RlpTxTag::To as u8,
            self.callee_address,
            idx,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::Value as u8,
            self.value,
            idx,
        );
        let idx = handle_bytes(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::DataPrefix as u8,
            RlpTxTag::Data as u8,
            &self.call_data,
            idx,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::ChainId as u8,
            self.chain_id.into(),
            idx,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::Zero as u8,
            0.into(),
            idx,
        );
        let idx = handle_u256(
            randomness,
            self.id,
            rlp_data.as_ref(),
            &mut rows,
            RlpDataType::TxSign,
            RlpTxTag::Zero as u8,
            0.into(),
            idx,
        );

        assert!(
            idx == rlp_data.len(),
            "RLP data mismatch: idx != len(rlp_data)"
        );
        rows
    }

    fn rlp_row(&self, randomness: F) -> RlpWitnessRow<F> {
        let rlp_out = rlp::encode(self);
        let rlc_rlp_out = rlp_out.as_ref().iter().fold(F::zero(), |acc, value| {
            acc * randomness + F::from(*value as u64)
        });

        RlpWitnessRow {
            id: self.id,
            index: rlp_out.len() + 1,
            data_type: RlpDataType::TxSign,
            value: 0,
            value_acc: rlc_rlp_out,
            tag: RlpTxTag::Rlp as u8,
            tag_length: 1,
            tag_index: 1,
            aux_tag_index: [0; 2],
            aux_tag_length: [0; 2],
            length_acc: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{arithmetic::Field, halo2curves::bn256::Fr};
    use num::Zero;

    use crate::evm_circuit::{
        test::rand_bytes,
        witness::{RlpTxTag, RlpWitnessGen, Transaction},
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
            chain_id: 4,
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
            chain_id: 1,
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
