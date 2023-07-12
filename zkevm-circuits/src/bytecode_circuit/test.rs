use crate::{
    bytecode_circuit::circuit::BytecodeCircuit,
    util::{log2_ceil, unusable_rows, SubCircuit},
    witness::BytecodeCollection,
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::{arithmetic::Field as Halo2Field, dev::MockProver, halo2curves::bn256::Fr};
use log::error;

use super::circuit::BytecodeCircuitRow;

#[test]
fn bytecode_circuit_unusable_rows() {
    assert_eq!(
        BytecodeCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, BytecodeCircuit::<Fr>>(()),
    )
}

impl<F: Field> BytecodeCircuit<F> {
    fn mut_rows(&mut self, mut mut_func: impl FnMut(&mut Vec<BytecodeCircuitRow<F>>)) -> Self {
        mut_func(&mut self.rows.0);
        self.clone()
    }

    fn from_bytes(bytecodes: impl Into<BytecodeCollection>, k: u32) -> Self {
        Self::new(bytecodes.into(), 2usize.pow(k))
    }

    fn verify(&self, success: bool) {
        let prover = MockProver::<F>::run(log2_ceil(self.size), self, Vec::new()).unwrap();
        let result = prover.verify_par();
        if let Err(failures) = &result {
            for failure in failures.iter() {
                error!("{}", failure);
            }
        }
        let error_msg = if success { "valid" } else { "invalid" };
        assert_eq!(result.is_ok(), success, "proof must be {}", error_msg);
    }
}

/// Tests a fully empty circuit
#[test]
fn bytecode_empty() {
    let k = 9;
    BytecodeCircuit::<Fr>::from_bytes(vec![vec![]], k).verify(true);
}

#[test]
fn bytecode_simple() {
    let k = 9;
    let bytecodes = vec![vec![7u8], vec![6u8], vec![5u8]];
    BytecodeCircuit::<Fr>::from_bytes(bytecodes, k).verify(true);
}

/// Tests a fully full circuit
#[test]
fn bytecode_full() {
    let k = 9;
    BytecodeCircuit::<Fr>::from_bytes(vec![vec![7u8; 2usize.pow(k) - 8]], k).verify(true);
}

#[test]
fn bytecode_last_row_with_byte() {
    let k = 9;
    // Last row must be a padding row, so we have one row less for actual bytecode
    BytecodeCircuit::<Fr>::from_bytes(vec![vec![7u8; 2usize.pow(k) - 7]], k).verify(false);
}

/// Tests a circuit with incomplete bytecode
#[test]
fn bytecode_incomplete() {
    let k = 9;
    BytecodeCircuit::<Fr>::from_bytes(vec![vec![7u8; 2usize.pow(k) + 1]], k).verify(false);
}

/// Tests multiple bytecodes in a single circuit
#[test]
fn bytecode_push() {
    let k = 9;
    BytecodeCircuit::<Fr>::from_bytes(
        vec![
            vec![],
            vec![OpcodeId::PUSH32.as_u8()],
            vec![OpcodeId::PUSH32.as_u8(), OpcodeId::ADD.as_u8()],
            vec![OpcodeId::ADD.as_u8(), OpcodeId::PUSH32.as_u8()],
            vec![
                OpcodeId::ADD.as_u8(),
                OpcodeId::PUSH32.as_u8(),
                OpcodeId::ADD.as_u8(),
            ],
        ],
        k,
    )
    .verify(true);
}

/// Test invalid code_hash data
#[test]
fn bytecode_invalid_hash_data() {
    let k = 9;
    let bytecodes = vec![vec![8u8, 2, 3, 8, 9, 7, 128]];
    // Change the code_hash on the first position (header row)
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes, k)
            .mut_rows(|rows| {
                let code_hash = rows[0].code_hash;
                rows[0].code_hash = code_hash.map(|limb| limb.map(|limb| limb + Fr::one()));
                log::trace!(
                    "bytecode_invalid_hash_data: Change the code_hash on the first position"
                );
            })
            .verify(false);
    }
    // TODO: other rows code_hash are ignored by the witness generation, to
    // test other rows invalid code_hash, we would need to inject an evil
    // witness.
}

/// Test invalid index
#[test]
#[ignore]
fn bytecode_invalid_index() {
    let k = 9;
    let bytecodes = vec![vec![8u8, 2, 3, 8, 9, 7, 128]];
    // Start the index at 1
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes.clone(), k)
            .mut_rows(|rows| {
                for row in rows.iter_mut() {
                    row.index += Fr::ONE;
                }
            })
            .verify(false);
    }
    // Don't increment an index once
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes, k)
            .mut_rows(|rows| {
                rows.last_mut().unwrap().index -= Fr::ONE;
            })
            .verify(false);
    }
}

/// Test invalid byte data
#[test]
fn bytecode_invalid_byte_data() {
    let k = 9;
    let bytecodes = vec![vec![8u8, 2, 3, 8, 9, 7, 128]];
    // Change the first byte
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes.clone(), k)
            .mut_rows(|rows| {
                rows[1].value = Fr::from(9u64);
            })
            .verify(false);
    }
    // Change a byte on another position
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes.clone(), k)
            .mut_rows(|rows| {
                rows[5].value = Fr::from(6u64);
            })
            .verify(false);
    }
    // Set a byte value out of range
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes, k)
            .mut_rows(|rows| {
                rows[3].value = Fr::from(256u64);
            })
            .verify(false);
    }
}

/// Test invalid is_code data
#[test]
fn bytecode_invalid_is_code() {
    let k = 9;
    let bytecodes = vec![vec![
        OpcodeId::ADD.as_u8(),
        OpcodeId::PUSH1.as_u8(),
        OpcodeId::PUSH1.as_u8(),
        OpcodeId::SUB.as_u8(),
        OpcodeId::PUSH7.as_u8(),
        OpcodeId::ADD.as_u8(),
        OpcodeId::PUSH6.as_u8(),
    ]];
    BytecodeCircuit::<Fr>::from_bytes(bytecodes.clone(), k).verify(true);
    // Mark the 3rd byte as code (is push data from the first PUSH1)
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes.clone(), k)
            .mut_rows(|rows| {
                rows[3].is_code = Fr::ONE;
            })
            .verify(false);
    }
    // Mark the 4rd byte as data (is code)
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes.clone(), k)
            .mut_rows(|rows| {
                rows[4].is_code = Fr::ZERO;
            })
            .verify(false);
    }
    // Mark the 7th byte as code (is data for the PUSH7)
    {
        BytecodeCircuit::<Fr>::from_bytes(bytecodes, k)
            .mut_rows(|rows| {
                rows[7].is_code = Fr::ONE;
            })
            .verify(false);
    }
}

#[test]
fn bytecode_soundness_bug_1() {
    let k = 9;
    let bytecodes = vec![vec![1, 2, 3, 4]];

    let bytecode_len = bytecodes[0].len();
    BytecodeCircuit::<Fr>::from_bytes(bytecodes, k)
        .mut_rows(|rows| {
            let code_hash = rows[0].code_hash.clone();
            let mut index = bytecode_len as u64;
            let size = 100;
            let minimum_rows = 8;
            let unrolled_len = rows.len();
            for i in unrolled_len..size - minimum_rows + 3 {
                rows.push(BytecodeCircuitRow::new(
                    i,
                    code_hash.clone(),
                    Fr::ONE,
                    Fr::from(index),
                    Fr::ONE,
                    Fr::from((i % 10 + 1) as u64),
                ));
                index += 1;
            }
        })
        .verify(false);
}
