use eth_types::{Field, ToLittleEndian, ToScalar, ZkEvmTransaction};
use halo2_proofs::circuit::Value;

use crate::{evm_circuit::util::rlc, table::TxContextFieldTag, util::Challenges};

/// Transaction in a witness block
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub tx: ZkEvmTransaction,
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
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::Nonce as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.eth_tx.nonce.as_u64())),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::Gas as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.eth_tx.gas.as_u64())),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::GasPrice as u64)),
                Value::known(F::zero()),
                challenges.evm_word().map(|challenge| {
                    rlc::value(&self.tx.eth_tx.gas_price.unwrap().to_le_bytes(), challenge)
                }),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::CallerAddress as u64)),
                Value::known(F::zero()),
                Value::known(self.tx.eth_tx.from.to_scalar().unwrap()),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::CalleeAddress as u64)),
                Value::known(F::zero()),
                Value::known(self.tx.eth_tx.to.unwrap().to_scalar().unwrap()),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::IsCreate as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.is_create as u64)),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::Value as u64)),
                Value::known(F::zero()),
                challenges
                    .evm_word()
                    .map(|challenge| rlc::value(&self.tx.eth_tx.value.to_le_bytes(), challenge)),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::CallDataLength as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.call_data_length as u64)),
            ],
            [
                Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                Value::known(F::from(TxContextFieldTag::CallDataGasCost as u64)),
                Value::known(F::zero()),
                Value::known(F::from(self.tx.call_data_gas_cost)),
            ],
        ];
        let tx_calldata = self
            .tx
            .eth_tx
            .input
            .iter()
            .enumerate()
            .map(|(idx, byte)| {
                [
                    Value::known(F::from(self.tx.eth_tx.transaction_index.unwrap().as_u64())),
                    Value::known(F::from(TxContextFieldTag::CallData as u64)),
                    Value::known(F::from(idx as u64)),
                    Value::known(F::from(*byte as u64)),
                ]
            })
            .collect();
        [tx_data, tx_calldata]
    }
}

// pub(super) fn tx_convert(tx: &circuit_input_builder::Transaction, id: usize) -> Transaction {
//     Transaction {
//         id,
//         nonce: tx.nonce,
//         gas: tx.gas,
//         gas_price: tx.gas_price,
//         caller_address: tx.from,
//         callee_address: tx.to,
//         is_create: tx.is_create(),
//         value: tx.value,
//         call_data: tx.input.clone(),
//         call_data_length: tx.input.len(),
//         call_data_gas_cost: tx
//             .input
//             .iter()
//             .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 }),
//         calls: tx
//             .calls()
//             .iter()
//             .map(|call| Call {
//                 id: call.call_id,
//                 is_root: call.is_root,
//                 is_create: call.is_create(),
//                 code_hash: call.code_hash.to_word(),
//                 rw_counter_end_of_reversion: call.rw_counter_end_of_reversion,
//                 caller_id: call.caller_id,
//                 depth: call.depth,
//                 caller_address: call.caller_address,
//                 callee_address: call.address,
//                 call_data_offset: call.call_data_offset,
//                 call_data_length: call.call_data_length,
//                 return_data_offset: call.return_data_offset,
//                 return_data_length: call.return_data_length,
//                 value: call.value,
//                 is_success: call.is_success,
//                 is_persistent: call.is_persistent,
//                 is_static: call.is_static,
//             })
//             .collect(),
//         steps: tx.steps().iter().map(step_convert).collect(),
//     }
// }
