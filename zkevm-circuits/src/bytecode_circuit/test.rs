use crate::{
    bytecode_circuit::{
        bytecode_unroller::*,
        circuit::{BytecodeCircuit, BytecodeTableAssignment},
    },
    table::BytecodeFieldTag,
    util::{is_push, unusable_rows, SubCircuit},
    witness::BytecodeCollection,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Bytecode, Field, Word};
use halo2_proofs::{arithmetic::Field as Halo2Field, dev::MockProver, halo2curves::bn256::Fr};
use log::error;

#[test]
fn bytecode_circuit_unusable_rows() {
    assert_eq!(
        BytecodeCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, BytecodeCircuit::<Fr>>(()),
    )
}

impl<F: Field> BytecodeCircuit<F> {
    pub(crate) fn verify(k: u32, bytecodes: &impl Into<BytecodeTableAssignment<F>>, success: bool) {
        let circuit = BytecodeCircuit::<F>::new(bytecodes, 2usize.pow(k));

        let prover = MockProver::<F>::run(k, &circuit, Vec::new()).unwrap();
        let result = prover.verify();
        if let Err(failures) = &result {
            for failure in failures.iter() {
                error!("{}", failure);
            }
        }
        assert_eq!(result.is_ok(), success);
    }
}

/// Test bytecode circuit with unrolled bytecode
pub fn test_bytecode_circuit_unrolled<F: Field>(
    k: u32,
    bytecodes: &impl Into<BytecodeTableAssignment<F>>,
    success: bool,
) {
    let circuit = BytecodeCircuit::<F>::new(bytecodes, 2usize.pow(k));

    let prover = MockProver::<F>::run(k, &circuit, Vec::new()).unwrap();
    let result = prover.verify_par();
    if let Err(failures) = &result {
        for failure in failures.iter() {
            error!("{}", failure);
        }
    }
    let error_msg = if success { "valid" } else { "invalid" };
    assert_eq!(result.is_ok(), success, "proof must be {}", error_msg);
}

/// Verify unrolling code
#[test]
fn bytecode_unrolling() {
    let k = 10;
    let mut rows = vec![];
    let mut bytecode = Bytecode::default();
    // First add all non-push bytes, which should all be seen as code
    for byte in 0u8..=255u8 {
        if !is_push(byte) {
            bytecode.write(byte, true);
            rows.push(BytecodeRow {
                code_hash: Word::zero(),
                tag: Fr::from(BytecodeFieldTag::Byte as u64),
                index: Fr::from(rows.len() as u64),
                is_code: Fr::from(true as u64),
                value: Fr::from(byte as u64),
            });
        }
    }
    // Now add the different push ops
    for n in 1..=32 {
        let data_byte = OpcodeId::PUSH32.as_u8();
        bytecode.push(
            n,
            Word::from_little_endian(&vec![data_byte; n as usize][..]),
        );
        rows.push(BytecodeRow {
            code_hash: Word::zero(),
            tag: Fr::from(BytecodeFieldTag::Byte as u64),
            index: Fr::from(rows.len() as u64),
            is_code: Fr::from(true as u64),
            value: Fr::from(OpcodeId::PUSH1.as_u64() + ((n - 1) as u64)),
        });
        for _ in 0..n {
            rows.push(BytecodeRow {
                code_hash: Word::zero(),
                tag: Fr::from(BytecodeFieldTag::Byte as u64),
                index: Fr::from(rows.len() as u64),
                is_code: Fr::from(false as u64),
                value: Fr::from(data_byte as u64),
            });
        }
    }
    // Set the code_hash of the complete bytecode in the rows
    let code_hash = bytecode.hash();
    for row in rows.iter_mut() {
        row.code_hash = code_hash;
    }
    rows.insert(
        0,
        BytecodeRow {
            code_hash,
            tag: Fr::from(BytecodeFieldTag::Header as u64),
            index: Fr::ZERO,
            is_code: Fr::ZERO,
            value: Fr::from(bytecode.codesize() as u64),
        },
    );
    // Unroll the bytecode
    let unrolled = unroll(bytecode.code());
    // Check if the bytecode was unrolled correctly
    assert_eq!(
        UnrolledBytecode {
            bytes: bytecode.code(),
            rows,
        },
        unrolled,
    );
    // Verify the unrolling in the circuit
    test_bytecode_circuit_unrolled::<Fr>(k, &vec![bytecode.code()], true);
}

/// Tests a fully empty circuit
#[test]
fn bytecode_empty() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(k, &vec![vec![]], true);
}

#[test]
fn bytecode_simple() {
    let k = 9;
    let bytecodes = vec![vec![7u8], vec![6u8], vec![5u8]];
    test_bytecode_circuit_unrolled::<Fr>(k, &bytecodes, true);
}

/// Tests a fully full circuit
#[test]
fn bytecode_full() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(k, &vec![vec![7u8; 2usize.pow(k) - 8]], true);
}

#[test]
fn bytecode_last_row_with_byte() {
    let k = 9;
    // Last row must be a padding row, so we have one row less for actual bytecode
    test_bytecode_circuit_unrolled::<Fr>(k, &vec![vec![7u8; 2usize.pow(k) - 7]], false);
}

/// Tests a circuit with incomplete bytecode
#[test]
fn bytecode_incomplete() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(k, &vec![vec![7u8; 2usize.pow(k) + 1]], false);
}

/// Tests multiple bytecodes in a single circuit
#[test]
fn bytecode_push() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(
        k,
        &vec![
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
        true,
    );
}

/// Test invalid code_hash data
#[test]
fn bytecode_invalid_hash_data() {
    let k = 9;
    let bytecodes = vec![vec![8u8, 2, 3, 8, 9, 7, 128]];
    test_bytecode_circuit_unrolled::<Fr>(k, &bytecodes, true);
    // Change the code_hash on the first position (header row)
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        let code_hash = invalid.0[0].code_hash;
        // Add 1 to both limbs
        invalid.0[0].code_hash = code_hash.map(|limb| limb.map(|limb| limb + Fr::one()));

        log::trace!("bytecode_invalid_hash_data: Change the code_hash on the first position");
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
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
    test_bytecode_circuit_unrolled::<Fr>(k, &bytecodes, true);
    // Start the index at 1
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        for row in invalid.0.iter_mut() {
            row.index += Fr::ONE;
        }
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
    // Don't increment an index once
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0.last_mut().unwrap().index -= Fr::ONE;
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
}

/// Test invalid byte data
#[test]
fn bytecode_invalid_byte_data() {
    let k = 9;
    let bytecodes = vec![vec![8u8, 2, 3, 8, 9, 7, 128]];
    test_bytecode_circuit_unrolled::<Fr>(k, &bytecodes, true);
    // Change the first byte
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0[1].value = Fr::from(9u64);
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
    // Change a byte on another position
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0[5].value = Fr::from(6u64);
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
    // Set a byte value out of range
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0[3].value = Fr::from(256u64);
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
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
    test_bytecode_circuit_unrolled::<Fr>(k, &bytecodes, true);
    // Mark the 3rd byte as code (is push data from the first PUSH1)
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0[3].is_code = Fr::ONE;
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
    // Mark the 4rd byte as data (is code)
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0[4].is_code = Fr::ZERO;
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
    // Mark the 7th byte as code (is data for the PUSH7)
    {
        let mut invalid: BytecodeTableAssignment<Fr> = bytecodes.into();
        invalid.0[7].is_code = Fr::ONE;
        test_bytecode_circuit_unrolled::<Fr>(k, &invalid, false);
    }
}

#[test]
#[should_panic]
#[allow(clippy::clone_on_copy)]
fn bytecode_soundness_bug_1() {
    let k = 9;
    let bytecode = vec![1, 2, 3, 4];
    let bytecode_len = bytecode.len();
    let unrolled: BytecodeTableAssignment<Fr> = vec![bytecode].into();
    let unrolled_len = unrolled.0.len();
    let code_hash = unrolled.0[0].code_hash.clone();
    let mut index = bytecode_len as u64;
    let size = 100;
    let minimum_rows = 8;

    let mut overwrite = unrolled.clone();
    for i in 0..size - minimum_rows + 3 {
        if i >= unrolled_len {
            overwrite.rows.push(BytecodeRow {
                code_hash: code_hash.clone(),
                tag: Fr::ONE,
                index: Fr::from(index),
                is_code: Fr::ONE,
                value: Fr::from((i % 10 + 1) as u64),
            });
            index += 1;
        }
    }
    let mut circuit = BytecodeCircuit::<Fr>::new(vec![unrolled], size);
    circuit.overwrite = overwrite;

    let prover = MockProver::<Fr>::run(k, &circuit, Vec::new()).unwrap();
    prover.assert_satisfied_par();
}
