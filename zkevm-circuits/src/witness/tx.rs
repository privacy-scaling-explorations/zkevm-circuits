use bus_mapping::circuit_input_builder;
use eth_types::{Field, ToLittleEndian, ToScalar, ZkEvmCall, ZkEvmExecStep, ZkEvmTransaction};
use halo2_proofs::circuit::Value;

use crate::{evm_circuit::util::rlc, table::TxContextFieldTag, util::Challenges};

use super::{step::step_convert, ExecStep};

/// Transaction in a witness block
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Transaction {
    /// Transaction
    pub tx: ZkEvmTransaction,
    /// Whether it's a create transaction
    pub is_create: bool,
    /// The call data length
    pub call_data_length: usize,
    /// The gas cost for transaction call data
    pub call_data_gas_cost: u64,
    /// The calls made in the transaction
    pub calls: Vec<ZkEvmCall>,
    /// The steps executioned in the transaction
    pub steps: Vec<ExecStep>,
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
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::Nonce as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.nonce as u64)),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::Gas as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.gas as u64)),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::GasPrice as u64)),
                Value::known(F::zero()),
                challenges
                    .evm_word()
                    .map(|challenge| rlc::value(&self.tx.gas_price.to_le_bytes(), challenge)),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::CallerAddress as u64)),
                Value::known(F::zero()),
                Value::known(self.tx.caller_address.to_scalar().unwrap()),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::CalleeAddress as u64)),
                Value::known(F::zero()),
                Value::known(self.tx.callee_address.to_scalar().unwrap()),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::IsCreate as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.is_create as u64)),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::Value as u64)),
                Value::known(F::zero()),
                challenges
                    .evm_word()
                    .map(|challenge| rlc::value(&self.tx.value.to_le_bytes(), challenge)),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::CallDataLength as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.call_data_length as u64)),
            ],
            [
                Value::known(F::from(self.tx.id as u64)),
                Value::known(F::from(TxContextFieldTag::CallDataGasCost as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.call_data_gas_cost)),
            ],
        ];
        let tx_calldata = self
            .tx
            .call_data
            .iter()
            .enumerate()
            .map(|(idx, byte)| {
                [
                    Value::known(F::from(self.tx.id as u64)),
                    Value::known(F::from(TxContextFieldTag::CallData as u64)),
                    Value::known(F::from(idx as u64)),
                    Value::known(F::from(*byte as u64)),
                ]
            })
            .collect();
        [tx_data, tx_calldata]
    }
}

pub(super) fn tx_convert(tx: &circuit_input_builder::Transaction, id: usize) -> Transaction {
    Transaction {
        tx: tx.tx.clone(),
        is_create: tx.is_create(),
        call_data_length: tx.tx.call_data.len(),
        call_data_gas_cost: tx
            .tx
            .call_data
            .iter()
            .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 }),
        calls: tx
            .calls()
            .iter()
            .map(|call| ZkEvmCall {
                id: call.call.id,
                is_root: call.call.is_root,
                is_create: call.is_create(),
                code_hash: call.call.code_hash,
                rw_counter_end_of_reversion: call.call.rw_counter_end_of_reversion,
                caller_id: call.call.caller_id,
                depth: call.call.depth,
                caller_address: call.call.caller_address,
                callee_address: call.call.callee_address,
                call_data_offset: call.call.call_data_offset,
                call_data_length: call.call.call_data_length,
                return_data_offset: call.call.return_data_offset,
                return_data_length: call.call.return_data_length,
                value: call.call.value,
                is_success: call.call.is_success,
                is_persistent: call.call.is_persistent,
                is_static: call.call.is_static,
            })
            .collect(),
        steps: tx.steps().iter().map(step_convert).collect(),
    }
}
