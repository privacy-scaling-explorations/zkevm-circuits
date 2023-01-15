#![allow(unused_imports)]
pub use crate::bytecode_circuit::bytecode_unroller::*;
use crate::table::{BytecodeFieldTag, BytecodeTable, KeccakTable};
use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use eth_types::Bytecode;
use eth_types::{evm_types::OpcodeId, Field, Word};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use log::error;

impl<F: Field> Circuit<F> for BytecodeCircuit<F> {
    type Config = (BytecodeCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let bytecode_table = BytecodeTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            BytecodeCircuitConfig::new(
                meta,
                BytecodeCircuitConfigArgs {
                    bytecode_table,
                    keccak_table,
                    challenges,
                },
            )
        };

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);

        config.keccak_table.dev_load(
            &mut layouter,
            self.bytecodes.iter().map(|b| &b.bytes),
            &challenges,
        )?;
        self.synthesize_sub(&config, &challenges, &mut layouter)?;
        Ok(())
    }
}

impl<F: Field> BytecodeCircuit<F> {
    /// Verify that the selected bytecode fulfills the circuit
    pub fn verify_raw(k: u32, bytecodes: Vec<Vec<u8>>) {
        let unrolled: Vec<_> = bytecodes.iter().map(|b| unroll(b.clone())).collect();
        Self::verify(k, unrolled, true);
    }

    pub(crate) fn verify(k: u32, bytecodes: Vec<UnrolledBytecode<F>>, success: bool) {
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
    bytecodes: Vec<UnrolledBytecode<F>>,
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
    assert_eq!(result.is_ok(), success);
}

fn get_randomness<F: Field>() -> F {
    F::from(123456)
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
    let code_hash = keccak(&bytecode.to_vec()[..]);
    for row in rows.iter_mut() {
        row.code_hash = code_hash;
    }
    rows.insert(
        0,
        BytecodeRow {
            code_hash,
            tag: Fr::from(BytecodeFieldTag::Length as u64),
            index: Fr::zero(),
            is_code: Fr::zero(),
            value: Fr::from(bytecode.to_vec().len() as u64),
        },
    );
    // Unroll the bytecode
    let unrolled = unroll(bytecode.to_vec());
    // Check if the bytecode was unrolled correctly
    assert_eq!(
        UnrolledBytecode {
            bytes: bytecode.to_vec(),
            rows,
        },
        unrolled,
    );
    // Verify the unrolling in the circuit
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled], true);
}

/// Tests a fully empty circuit
#[test]
fn bytecode_empty() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![])], true);
}

#[test]
fn bytecode_simple() {
    let k = 9;
    let bytecodes = vec![unroll(vec![7u8]), unroll(vec![6u8]), unroll(vec![5u8])];
    test_bytecode_circuit_unrolled::<Fr>(k, bytecodes, true);
}

/// Tests a fully full circuit
#[test]
fn bytecode_full() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) - 7])], true);
}

/// Tests a circuit with incomplete bytecode
#[test]
fn bytecode_incomplete() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) + 1])], false);
}

/// Tests multiple bytecodes in a single circuit
#[test]
fn bytecode_push() {
    let k = 9;
    test_bytecode_circuit_unrolled::<Fr>(
        k,
        vec![
            unroll(vec![]),
            unroll(vec![OpcodeId::PUSH32.as_u8()]),
            unroll(vec![OpcodeId::PUSH32.as_u8(), OpcodeId::ADD.as_u8()]),
            unroll(vec![OpcodeId::ADD.as_u8(), OpcodeId::PUSH32.as_u8()]),
            unroll(vec![
                OpcodeId::ADD.as_u8(),
                OpcodeId::PUSH32.as_u8(),
                OpcodeId::ADD.as_u8(),
            ]),
        ],
        true,
    );
}

/// Test invalid code_hash data
#[test]
fn bytecode_invalid_hash_data() {
    let k = 9;
    let bytecode = vec![8u8, 2, 3, 8, 9, 7, 128];
    let unrolled = unroll(bytecode);
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
    // Change the code_hash on the first position
    {
        let mut invalid = unrolled.clone();
        invalid.rows[0].code_hash += Word::one();
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Change the code_hash on another position
    {
        let mut invalid = unrolled.clone();
        invalid.rows[4].code_hash += Word::one();
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Change all the hashes so it doesn't match the keccak lookup code_hash
    {
        let mut invalid = unrolled;
        for row in invalid.rows.iter_mut() {
            row.code_hash = Word::one();
        }
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
}

/// Test invalid index
#[test]
#[ignore]
fn bytecode_invalid_index() {
    let k = 9;
    let bytecode = vec![8u8, 2, 3, 8, 9, 7, 128];
    let unrolled = unroll(bytecode);
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
    // Start the index at 1
    {
        let mut invalid = unrolled.clone();
        for row in invalid.rows.iter_mut() {
            row.index += Fr::one();
        }
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Don't increment an index once
    {
        let mut invalid = unrolled;
        invalid.rows.last_mut().unwrap().index -= Fr::one();
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
}

/// Test invalid byte data
#[test]
fn bytecode_invalid_byte_data() {
    let k = 9;
    let bytecode = vec![8u8, 2, 3, 8, 9, 7, 128];
    let unrolled = unroll(bytecode);
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
    // Change the first byte
    {
        let mut invalid = unrolled.clone();
        invalid.rows[1].value = Fr::from(9u64);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Change a byte on another position
    {
        let mut invalid = unrolled.clone();
        invalid.rows[5].value = Fr::from(6u64);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Set a byte value out of range
    {
        let mut invalid = unrolled;
        invalid.rows[3].value = Fr::from(256u64);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
}

/// Test invalid is_code data
#[test]
fn bytecode_invalid_is_code() {
    let k = 9;
    let bytecode = vec![
        OpcodeId::ADD.as_u8(),
        OpcodeId::PUSH1.as_u8(),
        OpcodeId::PUSH1.as_u8(),
        OpcodeId::SUB.as_u8(),
        OpcodeId::PUSH7.as_u8(),
        OpcodeId::ADD.as_u8(),
        OpcodeId::PUSH6.as_u8(),
    ];
    let unrolled = unroll(bytecode);
    test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
    // Mark the 3rd byte as code (is push data from the first PUSH1)
    {
        let mut invalid = unrolled.clone();
        invalid.rows[3].is_code = Fr::one();
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Mark the 4rd byte as data (is code)
    {
        let mut invalid = unrolled.clone();
        invalid.rows[4].is_code = Fr::zero();
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
    // Mark the 7th byte as code (is data for the PUSH7)
    {
        let mut invalid = unrolled;
        invalid.rows[7].is_code = Fr::one();
        test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
    }
}
