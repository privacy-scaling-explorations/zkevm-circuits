use bus_mapping::circuit_input_builder;
use eth_types::{
    sign_types::SignData, Address, Field, ToBigEndian, ToLittleEndian, ToScalar, Word, H256,
};
use halo2_proofs::circuit::Value;

use crate::{
    evm_circuit::util::rlc,
    table::TxContextFieldTag,
    util::{rlc_be_bytes, Challenges},
};

use super::{Call, ExecStep};

/// Transaction in a witness block
#[derive(Debug, Default, Clone)]
pub struct Transaction {
    /// The transaction identifier in the block
    pub id: usize,
    /// The sender account nonce of the transaction
    pub nonce: u64,
    /// The gas limit of the transaction
    pub gas: u64,
    /// The gas price
    pub gas_price: Word,
    /// The caller address
    pub caller_address: Address,
    /// The callee address
    pub callee_address: Address,
    /// Whether it's a create transaction
    pub is_create: bool,
    /// The ether amount of the transaction
    pub value: Word,
    /// The call data
    pub call_data: Vec<u8>,
    /// The call data length
    pub call_data_length: usize,
    /// The gas cost for transaction call data
    pub call_data_gas_cost: u64,
    /// The calls made in the transaction
    pub calls: Vec<Call>,
    /// The steps executioned in the transaction
    pub steps: Vec<ExecStep>,
    /// "v" value of the transaction signature
    pub v: u64,
    /// "r" value of the transaction signature
    pub r: Word,
    /// "s" value of the transaction signature
    pub s: Word,
    /// tx sign hash
    pub tx_sign_hash: H256,
}

impl Transaction {
    /// Assignments for tx table, split into tx_data (all fields except
    /// calldata) and tx_calldata
    pub fn table_assignments<F: Field>(
        &self,
        challenges: Challenges<Value<F>>,
    ) -> [Vec<[Value<F>; 4]>; 2] {
        let tx_data = vec![
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::Nonce as u64)),
                Value::known(F::ZERO),
                Value::known(F::from(self.nonce)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::Gas as u64)),
                Value::known(F::ZERO),
                Value::known(F::from(self.gas)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::GasPrice as u64)),
                Value::known(F::ZERO),
                challenges
                    .evm_word()
                    .map(|challenge| rlc::value(&self.gas_price.to_le_bytes(), challenge)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::CallerAddress as u64)),
                Value::known(F::ZERO),
                Value::known(self.caller_address.to_scalar().unwrap()),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::CalleeAddress as u64)),
                Value::known(F::ZERO),
                Value::known(self.callee_address.to_scalar().unwrap()),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::IsCreate as u64)),
                Value::known(F::ZERO),
                Value::known(F::from(self.is_create as u64)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::Value as u64)),
                Value::known(F::ZERO),
                challenges
                    .evm_word()
                    .map(|challenge| rlc::value(&self.value.to_le_bytes(), challenge)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::CallDataLength as u64)),
                Value::known(F::ZERO),
                Value::known(F::from(self.call_data_length as u64)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::CallDataGasCost as u64)),
                Value::known(F::ZERO),
                Value::known(F::from(self.call_data_gas_cost)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::TxSignHash as u64)),
                Value::known(F::ZERO),
                challenges
                    .evm_word()
                    .map(|challenge| rlc::value(&self.tx_sign_hash.to_fixed_bytes(), challenge)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::SigV as u64)),
                Value::known(F::ZERO),
                Value::known(F::from(self.v)),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::SigR as u64)),
                Value::known(F::ZERO),
                rlc_be_bytes(&self.r.to_be_bytes(), challenges.evm_word()),
            ],
            [
                Value::known(F::from(self.id as u64)),
                Value::known(F::from(TxContextFieldTag::SigS as u64)),
                Value::known(F::ZERO),
                rlc_be_bytes(&self.s.to_be_bytes(), challenges.evm_word()),
            ],
        ];
        let tx_calldata = self
            .call_data
            .iter()
            .enumerate()
            .map(|(idx, byte)| {
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::CallData as u64)),
                    Value::known(F::from(idx as u64)),
                    Value::known(F::from(*byte as u64)),
                ]
            })
            .collect();
        [tx_data, tx_calldata]
    }
}

pub(super) fn tx_convert(
    tx: &circuit_input_builder::Transaction,
    chain_id: u64,
    id: usize,
) -> Transaction {
    let sign_data: SignData = tx
        .tx
        .sign_data(chain_id)
        .expect("Error computing tx_sign_hash");
    let tx_sign_hash = H256::from(&sign_data.msg_hash.to_bytes());
    Transaction {
        id,
        nonce: tx.tx.nonce.as_u64(),
        gas: tx.gas(),
        gas_price: tx.tx.gas_price,
        caller_address: tx.tx.from,
        callee_address: tx.tx.to_or_contract_addr(),
        is_create: tx.is_create(),
        value: tx.tx.value,
        call_data: tx.tx.call_data.to_vec(),
        call_data_length: tx.tx.call_data.len(),
        call_data_gas_cost: tx.tx.call_data_gas_cost(),
        calls: tx.calls().to_vec(),
        steps: tx.steps().to_vec(),
        v: tx.tx.v,
        r: tx.tx.r,
        s: tx.tx.s,
        tx_sign_hash,
    }
}
