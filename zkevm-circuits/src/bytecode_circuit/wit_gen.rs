use eth_types::{Field, ToLittleEndian};
use halo2_proofs::circuit::Value;

use crate::{
    evm_circuit::util::rlc,
    util::{get_push_size, Challenges},
};

use super::bytecode_unroller::UnrolledBytecode;

#[derive(Debug, Clone)]
pub struct BytecodeWitnessGen<F: Field> {
    bytecode: UnrolledBytecode<F>,
    challenges: Challenges<Value<F>>,
    idx: usize,

    pub push_data_left: u64,
    pub next_push_data_left: u64,
    pub push_data_size: u64,
    pub length: usize,
    pub value_rlc: Value<F>,
    pub code_hash: Value<F>,
}

impl<F: Field> BytecodeWitnessGen<F> {
    pub fn new(
        bytecode: &UnrolledBytecode<F>,
        challenges: &Challenges<Value<F>>,
    ) -> BytecodeWitnessGen<F> {
        BytecodeWitnessGen {
            bytecode: bytecode.clone(),
            challenges: *challenges,
            idx: 1,
            push_data_left: 0,
            next_push_data_left: 0,
            push_data_size: 0,
            length: bytecode.bytes.len(),
            value_rlc: challenges.keccak_input().map(|_| F::zero()),
            code_hash: challenges
                .evm_word()
                .map(|challenge| rlc::value(&bytecode.rows[0].code_hash.to_le_bytes(), challenge)),
        }
    }

    pub fn next_row(&mut self) {
        if self.idx > 1 {
            self.push_data_left = self.next_push_data_left;
        }
        if self.idx > 0 {
            let row = self.bytecode.rows[self.idx].clone();
            let is_code = self.push_data_left == 0;

            self.push_data_size = get_push_size(row.value.get_lower_128() as u8);

            self.next_push_data_left = if is_code {
                self.push_data_size
            } else {
                self.push_data_left - 1
            };

            self.value_rlc
                .as_mut()
                .zip(self.challenges.keccak_input())
                .map(|(value_rlc, challenge)| *value_rlc = (*value_rlc * challenge) + row.value);
        }

        self.idx += 1;
    }

    pub fn has_more(&self) -> bool {
        self.length > self.idx - 1
    }

    pub fn index(&self) -> F {
        self.bytecode.rows[self.idx - 1].index
    }

    pub fn value(&self) -> F {
        self.bytecode.rows[self.idx - 1].value
    }

    pub fn is_code(&self) -> F {
        self.bytecode.rows[self.idx - 1].is_code
    }
}
