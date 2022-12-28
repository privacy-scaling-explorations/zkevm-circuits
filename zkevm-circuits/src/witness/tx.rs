use bus_mapping::circuit_input_builder;
use eth_types::{Address, Field, ToLittleEndian, ToScalar, ToWord, Word};
use halo2_proofs::circuit::Value;

use crate::{
    evm_circuit::util::RandomLinearCombination, table::TxContextFieldTag, util::Challenges,
};

use super::{step::step_convert, Call, ExecStep};

/// Transaction in a witness block
#[derive(Debug, Default, Clone, PartialEq, Eq)]
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
}

impl Transaction {
    /// Assignments for tx table
    pub fn table_assignments<F: Field>(
        &self,
        challenges: Challenges<Value<F>>,
    ) -> Vec<[Value<F>; 4]> {
        [
            vec![
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::Nonce as u64)),
                    Value::known(F::zero()),
                    Value::known(F::from(self.nonce)),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::Gas as u64)),
                    Value::known(F::zero()),
                    Value::known(F::from(self.gas)),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::GasPrice as u64)),
                    Value::known(F::zero()),
                    challenges.evm_word().map(|evm_word| {
                        RandomLinearCombination::random_linear_combine(
                            self.gas_price.to_le_bytes(),
                            evm_word,
                        )
                    }),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::CallerAddress as u64)),
                    Value::known(F::zero()),
                    Value::known(self.caller_address.to_scalar().unwrap()),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::CalleeAddress as u64)),
                    Value::known(F::zero()),
                    Value::known(self.callee_address.to_scalar().unwrap()),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::IsCreate as u64)),
                    Value::known(F::zero()),
                    Value::known(F::from(self.is_create as u64)),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::Value as u64)),
                    Value::known(F::zero()),
                    challenges.evm_word().map(|evm_word| {
                        RandomLinearCombination::random_linear_combine(
                            self.value.to_le_bytes(),
                            evm_word,
                        )
                    }),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::CallDataLength as u64)),
                    Value::known(F::zero()),
                    Value::known(F::from(self.call_data_length as u64)),
                ],
                [
                    Value::known(F::from(self.id as u64)),
                    Value::known(F::from(TxContextFieldTag::CallDataGasCost as u64)),
                    Value::known(F::zero()),
                    Value::known(F::from(self.call_data_gas_cost)),
                ],
            ],
            self.call_data
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
                .collect(),
        ]
        .concat()
    }
}

pub(super) fn tx_convert(tx: &circuit_input_builder::Transaction, id: usize) -> Transaction {
    Transaction {
        id,
        nonce: tx.nonce,
        gas: tx.gas,
        gas_price: tx.gas_price,
        caller_address: tx.from,
        callee_address: tx.to,
        is_create: tx.is_create(),
        value: tx.value,
        call_data: tx.input.clone(),
        call_data_length: tx.input.len(),
        call_data_gas_cost: tx
            .input
            .iter()
            .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 }),
        calls: tx
            .calls()
            .iter()
            .map(|call| Call {
                id: call.call_id,
                is_root: call.is_root,
                is_create: call.is_create(),
                code_hash: call.code_hash.to_word(),
                rw_counter_end_of_reversion: call.rw_counter_end_of_reversion,
                caller_id: call.caller_id,
                depth: call.depth,
                caller_address: call.caller_address,
                callee_address: call.address,
                call_data_offset: call.call_data_offset,
                call_data_length: call.call_data_length,
                return_data_offset: call.return_data_offset,
                return_data_length: call.return_data_length,
                value: call.value,
                is_success: call.is_success,
                is_persistent: call.is_persistent,
                is_static: call.is_static,
            })
            .collect(),
        steps: tx.steps().iter().map(step_convert).collect(),
    }
}
