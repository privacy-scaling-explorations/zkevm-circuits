use crate::{
    table::BytecodeFieldTag,
    util::{get_push_size, keccak},
};
use eth_types::{Field, Word};
use std::vec;

#[cfg(feature = "onephase")]
use halo2_proofs::plonk::FirstPhase as SecondPhase;
#[cfg(not(feature = "onephase"))]
use halo2_proofs::plonk::SecondPhase;

/// Public data for the bytecode
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct BytecodeRow<F: Field> {
    pub(crate) code_hash: Word,
    pub(crate) tag: F,
    pub(crate) index: F,
    pub(crate) is_code: F,
    pub(crate) value: F,
}

/// Unrolled bytecode
#[derive(Clone, Debug, PartialEq)]
pub struct UnrolledBytecode<F: Field> {
    pub(crate) bytes: Vec<u8>,
    pub(crate) rows: Vec<BytecodeRow<F>>,
}
        #[cfg(feature = "codehash")]
            use crate::table::DynamicTableColumns;
        let mut is_first_time = true;

                if is_first_time {
                    is_first_time = false;
                    self.set_row(
                        &mut region,
                        &push_rindex_is_zero_chip,
                        &length_is_zero_chip,
                        last_row_offset,
                        false,
                        true,
                        Value::known(F::zero()),
                        F::from(BytecodeFieldTag::Padding as u64),
                        F::zero(),
                        F::one(),
                        F::zero(),
                        0,
                        Value::known(F::zero()),
                        F::zero(),
                        F::zero(),
                        true,
                        true,
                        F::zero(),
                    )?;
                    return Ok(());
                }

                        if idx == bytecode.rows.len() - 1 {
                            log::trace!("bytecode len {}", bytecode.rows.len());
                            log::trace!(
                                "assign bytecode circuit at {}: codehash {:?}, rlc {:?}",
                                offset,
                                row.code_hash.to_le_bytes(),
                                code_hash
                            );
                        }
                        if idx == bytecode.rows.len() - 1 {
                            log::trace!("assign bytecode circuit: input rlc {:?}", hash_input_rlc);
                        }

            log::debug!("bytecode circuit q_last at {}", offset);

/// Get unrolled bytecode from raw bytes
pub fn unroll<F: Field>(bytes: Vec<u8>) -> UnrolledBytecode<F> {
    let code_hash = keccak(&bytes[..]);
    unroll_with_codehash(code_hash, bytes)
}

/// Get unrolled bytecode from raw bytes and codehash
pub fn unroll_with_codehash<F: Field>(code_hash: U256, bytes: Vec<u8>) -> UnrolledBytecode<F> {
    let mut rows = vec![BytecodeRow::<F> {
        code_hash,
        tag: F::from(BytecodeFieldTag::Header as u64),
        index: F::zero(),
        is_code: F::zero(),
        value: F::from(bytes.len() as u64),
    }];
    // Run over all the bytes
    let mut push_rindex = 0;
    for (index, byte) in bytes.iter().enumerate() {
        // Track which byte is an opcode and which is push data
        let is_code = push_rindex == 0;
        push_rindex = if is_code {
            get_push_size(*byte)
        } else {
            push_rindex - 1
        };

        rows.push(BytecodeRow::<F> {
            code_hash,
            tag: F::from(BytecodeFieldTag::Byte as u64),
            index: F::from(index as u64),
            is_code: F::from(is_code as u64),
            value: F::from(*byte as u64),
        });
    }
    UnrolledBytecode { bytes, rows }
}
/// test module
#[cfg(any(feature = "test", test))]
        F::from(DEFAULT_RAND as u64)
    #[ignore = "this test needs to set fail_fast to false"]
    #[ignore]
    #[ignore]
