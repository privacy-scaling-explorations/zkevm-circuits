use super::{StateCircuit, StateConfig};
use crate::evm_circuit::{
    table::{AccountFieldTag, CallContextFieldTag, TxLogFieldTag},
    witness::{Rw, RwMap},
};
use crate::state_circuit::binary_number::AsBits;
use bus_mapping::operation::{
    MemoryOp, Operation, OperationContainer, RWCounter, StackOp, StorageOp, RW,
};
use eth_types::{
    address,
    evm_types::{MemoryAddress, StackAddress},
    Address, ToAddress, Word, U256,
};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::{
    arithmetic::BaseExt,
    dev::{MockProver, VerifyFailure},
    pairing::bn256::{Bn256, Fr, G1Affine},
    plonk::{keygen_vk, Advice, Circuit, Column, ConstraintSystem},
};
use std::collections::{BTreeSet, HashMap};

const N_ROWS: usize = 1 << 16;

#[derive(Hash, Eq, PartialEq)]
pub enum AdviceColumn {
    IsWrite,
    Address,
    AddressLimb0,
    AddressLimb1,
    StorageKey,
    StorageKeyByte0,
    StorageKeyByte1,
    Value,
    RwCounter,
    RwCounterLimb0,
    RwCounterLimb1,
    TagBit0,
    TagBit1,
    TagBit2,
    TagBit3,
    LimbIndexBit0,
    LimbIndexBit1,
    LimbIndexBit2,
    LimbIndexBit3,
    LimbIndexBit4,
}

impl AdviceColumn {
    pub fn value(&self, config: &StateConfig) -> Column<Advice> {
        match self {
            Self::IsWrite => config.is_write,
            Self::Address => config.sort_keys.address.value,
            Self::AddressLimb0 => config.sort_keys.address.limbs[0],
            Self::AddressLimb1 => config.sort_keys.address.limbs[1],
            Self::StorageKey => config.sort_keys.storage_key.encoded,
            Self::StorageKeyByte0 => config.sort_keys.storage_key.bytes[0],
            Self::StorageKeyByte1 => config.sort_keys.storage_key.bytes[1],
            Self::Value => config.value,
            Self::RwCounter => config.sort_keys.rw_counter.value,
            Self::RwCounterLimb0 => config.sort_keys.rw_counter.limbs[0],
            Self::RwCounterLimb1 => config.sort_keys.rw_counter.limbs[1],
            Self::TagBit0 => config.sort_keys.tag.bits[0],
            Self::TagBit1 => config.sort_keys.tag.bits[1],
            Self::TagBit2 => config.sort_keys.tag.bits[2],
            Self::TagBit3 => config.sort_keys.tag.bits[3],
            Self::LimbIndexBit0 => config.lexicographic_ordering.first_different_limb.bits[0],
            Self::LimbIndexBit1 => config.lexicographic_ordering.first_different_limb.bits[1],
            Self::LimbIndexBit2 => config.lexicographic_ordering.first_different_limb.bits[2],
            Self::LimbIndexBit3 => config.lexicographic_ordering.first_different_limb.bits[3],
            Self::LimbIndexBit4 => config.lexicographic_ordering.first_different_limb.bits[4],
        }
    }
}

fn test_state_circuit_ok(
    memory_ops: Vec<Operation<MemoryOp>>,
    stack_ops: Vec<Operation<StackOp>>,
    storage_ops: Vec<Operation<StorageOp>>,
) {
    let rw_map = RwMap::from(&OperationContainer {
        memory: memory_ops,
        stack: stack_ops,
        storage: storage_ops,
        ..Default::default()
    });

    let randomness = Fr::rand();
    let circuit = StateCircuit::<Fr, N_ROWS>::new(randomness, rw_map);
    let power_of_randomness = circuit.instance();

    let prover = MockProver::<Fr>::run(19, &circuit, power_of_randomness).unwrap();
    let verify_result = prover.verify();
    assert_eq!(verify_result, Ok(()));
}

#[test]
fn degree() {
    let mut meta = ConstraintSystem::<Fr>::default();
    StateCircuit::<Fr, N_ROWS>::configure(&mut meta);
    assert_eq!(meta.degree(), 9);
}

#[test]
fn verifying_key_independent_of_rw_length() {
    let randomness = Fr::rand();
    let degree = 17;
    let params = Params::<G1Affine>::unsafe_setup::<Bn256>(degree);

    let no_rows = StateCircuit::<Fr, N_ROWS>::new(randomness, RwMap::default());
    let one_row = StateCircuit::<Fr, N_ROWS>::new(
        randomness,
        RwMap::from(&OperationContainer {
            memory: vec![Operation::new(
                RWCounter::from(1),
                RW::WRITE,
                MemoryOp::new(1, MemoryAddress::from(0), 32),
            )],
            ..Default::default()
        }),
    );

    // halo2::plonk::VerifyingKey doesn't derive Eq, so we check for equality using
    // its debug string.
    assert_eq!(
        format!("{:?}", keygen_vk(&params, &no_rows).unwrap()),
        format!("{:?}", keygen_vk(&params, &one_row).unwrap())
    );
}

#[test]
fn state_circuit_simple_2() {
    let memory_op_0 = Operation::new(
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let memory_op_1 = Operation::new(
        RWCounter::from(24),
        RW::READ,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );

    let memory_op_2 = Operation::new(
        RWCounter::from(17),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(1), 32),
    );
    let memory_op_3 = Operation::new(
        RWCounter::from(87),
        RW::READ,
        MemoryOp::new(1, MemoryAddress::from(1), 32),
    );

    let stack_op_0 = Operation::new(
        RWCounter::from(17),
        RW::WRITE,
        StackOp::new(1, StackAddress::from(1), Word::from(32)),
    );
    let stack_op_1 = Operation::new(
        RWCounter::from(87),
        RW::READ,
        StackOp::new(1, StackAddress::from(1), Word::from(32)),
    );

    let storage_op_0 = Operation::new(
        RWCounter::from(0),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::zero(),
            1usize,
            Word::zero(),
        ),
    );
    let storage_op_1 = Operation::new(
        RWCounter::from(18),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::from(32),
            1usize,
            Word::from(32),
        ),
    );
    let storage_op_2 = Operation::new(
        RWCounter::from(19),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::from(32),
            1usize,
            Word::from(32),
        ),
    );

    test_state_circuit_ok(
        vec![memory_op_0, memory_op_1, memory_op_2, memory_op_3],
        vec![stack_op_0, stack_op_1],
        vec![storage_op_0, storage_op_1, storage_op_2],
    );
}

#[test]
fn state_circuit_simple_6() {
    let memory_op_0 = Operation::new(
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let memory_op_1 = Operation::new(
        RWCounter::from(13),
        RW::READ,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let storage_op_2 = Operation::new(
        RWCounter::from(19),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::from(32),
            1usize,
            Word::from(32),
        ),
    );
    test_state_circuit_ok(vec![memory_op_0, memory_op_1], vec![], vec![storage_op_2]);
}

#[test]
fn lexicographic_ordering_test_1() {
    let memory_op = Operation::new(
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let storage_op = Operation::new(
        RWCounter::from(19),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::from(32),
            1usize,
            Word::from(32),
        ),
    );
    test_state_circuit_ok(vec![memory_op], vec![], vec![storage_op]);
}

#[test]
fn lexicographic_ordering_test_2() {
    let memory_op_0 = Operation::new(
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let memory_op_1 = Operation::new(
        RWCounter::from(13),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    test_state_circuit_ok(vec![memory_op_0, memory_op_1], vec![], vec![]);
}

#[test]
fn first_access_for_stack_is_write() {
    let rows = vec![
        Rw::Stack {
            rw_counter: 24,
            is_write: true,
            call_id: 1,
            stack_pointer: 1022,
            value: U256::from(394500u64),
        },
        Rw::Stack {
            rw_counter: 25,
            is_write: false,
            call_id: 1,
            stack_pointer: 1022,
            value: U256::from(394500u64),
        },
    ];

    assert_eq!(verify(rows), Ok(()));
}

#[test]
fn diff_1_problem_repro() {
    let rows = vec![
        Rw::Account {
            rw_counter: 1,
            is_write: true,
            account_address: Address::default(),
            field_tag: AccountFieldTag::CodeHash,
            value: U256::zero(),
            value_prev: U256::zero(),
        },
        Rw::Account {
            rw_counter: 2,
            is_write: true,
            account_address: Address::default(),
            field_tag: AccountFieldTag::CodeHash,
            value: U256::zero(),
            value_prev: U256::zero(),
        },
    ];

    assert_eq!(verify(rows), Ok(()));
}

#[test]
fn storage_key_rlc() {
    let rows = vec![Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::from(256),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    }];

    assert_eq!(verify(rows), Ok(()));
}

#[test]
fn tx_log_ok() {
    let rows = vec![
        Rw::TxLog {
            rw_counter: 1,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Data,
            index: 0usize,
            value: U256::from(3u64),
        },
        Rw::TxLog {
            rw_counter: 3,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Data,
            index: 1usize,
            value: U256::from(3u64),
        },
        Rw::TxLog {
            rw_counter: 4,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 5,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 1usize,
            value: U256::from(2u64),
        },
        /* TODO: after issue https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/561
         * resolved, we can test tx_id increases' cases */
        /*  Rw::TxLog {
         *     rw_counter: 4,
         *     is_write: true,
         *     tx_id: 2,
         *     log_id: 1,
         *     field_tag: TxLogFieldTag::Address,
         *     index: 0 as usize,
         *     value: U256::from(10u64),
         *  }, */
    ];

    assert_eq!(verify(rows), Ok(()));
}

/// negative tests for tx log
#[test]
fn tx_log_index_not_increase_by_1() {
    let rows = vec![
        Rw::TxLog {
            rw_counter: 1,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 3,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 2usize,
            value: U256::from(2u64),
        },
    ];

    //assert_eq!(verify(rows), Ok(()));
    assert_error_matches(verify(rows), "index = pre_index + 1");
}

///topic_index in range [0,4)
#[test]
fn tx_log_index_out_of_range() {
    let rows = vec![
        Rw::TxLog {
            rw_counter: 1,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 5usize,
            value: U256::one(),
        },
    ];

    //assert_eq!(verify(rows), Ok(()));
    assert_error_matches(verify(rows), "topic_index in range [0,4)");
}

/// for address field index is zero
#[test]
fn tx_log_address_field_invalid_index() {
    let rows = vec![
        Rw::TxLog {
            rw_counter: 1,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 1usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 0usize,
            value: U256::one(),
        },
    ];

    assert_error_matches(verify(rows), "index is zero for address");
}

/// within tx for non address field tag row, log id not change
#[test]
fn tx_log_id_change_within_tx() {
    let rows = vec![
        Rw::TxLog {
            rw_counter: 1,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 3,
            is_write: true,
            tx_id: 1,
            log_id: 2,
            field_tag: TxLogFieldTag::Topic,
            index: 1usize,
            value: U256::one(),
        },
    ];

    assert_error_matches(
        verify(rows),
        "log_id will not change if field_tag != Address within tx",
    );
}

#[test]
fn address_limb_mismatch() {
    let rows = vec![Rw::Account {
        rw_counter: 1,
        is_write: false,
        account_address: address!("0x000000000000000000000000000000000cafe002"),
        field_tag: AccountFieldTag::CodeHash,
        value: U256::zero(),
        value_prev: U256::zero(),
    }];
    let overrides = HashMap::from([((AdviceColumn::Address, 0), Fr::from(10))]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "mpi value matches claimed limbs");
}

#[test]
fn address_limb_out_of_range() {
    let rows = vec![Rw::Account {
        rw_counter: 1,
        is_write: false,
        account_address: address!("0x0000000000000000000000000000000000010000"),
        field_tag: AccountFieldTag::CodeHash,
        value: U256::zero(),
        value_prev: U256::zero(),
    }];
    let overrides = HashMap::from([
        ((AdviceColumn::AddressLimb0, 0), Fr::from(1 << 16)),
        ((AdviceColumn::AddressLimb1, 0), Fr::zero()),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "mpi limb fits into u16");
}

#[test]
fn storage_key_mismatch() {
    let rows = vec![Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::from(6),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    }];
    let overrides = HashMap::from([((AdviceColumn::StorageKey, 0), Fr::from(10))]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "rlc encoded value matches bytes");
}

#[test]
fn storage_key_byte_out_of_range() {
    let rows = vec![Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::from(256),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    }];
    let overrides = HashMap::from([
        ((AdviceColumn::StorageKey, 0), Fr::from(256)),
        ((AdviceColumn::StorageKeyByte0, 0), Fr::from(256)),
        ((AdviceColumn::StorageKeyByte1, 0), Fr::zero()),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "rlc bytes fit into u8");
}

#[test]
fn is_write_nonbinary() {
    let rows = vec![Rw::CallContext {
        rw_counter: 1,
        is_write: false,
        call_id: 0,
        field_tag: CallContextFieldTag::TxId,
        value: U256::one(),
    }];
    let overrides = HashMap::from([((AdviceColumn::IsWrite, 0), Fr::from(4))]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "is_write is boolean");
}

#[test]
fn nonlexicographic_order_tag() {
    let first = Rw::Memory {
        rw_counter: 1,
        is_write: true,
        call_id: 1,
        memory_address: 10,
        byte: 12,
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: false,
        call_id: 1,
        field_tag: CallContextFieldTag::IsSuccess,
        value: U256::one(),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_field_tag() {
    let first = Rw::CallContext {
        rw_counter: 5,
        is_write: false,
        call_id: 0,
        field_tag: CallContextFieldTag::RwCounterEndOfReversion,
        value: U256::from(100),
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: false,
        call_id: 0,
        field_tag: CallContextFieldTag::CallerId,
        value: U256::from(200),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_id() {
    let first = Rw::CallContext {
        rw_counter: 1,
        is_write: false,
        call_id: 0,
        field_tag: CallContextFieldTag::RwCounterEndOfReversion,
        value: U256::from(100),
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: false,
        call_id: 1,
        field_tag: CallContextFieldTag::RwCounterEndOfReversion,
        value: U256::from(200),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_address() {
    let first = Rw::Account {
        rw_counter: 50,
        is_write: true,
        account_address: address!("0x1000000000000000000000000000000000000000"),
        field_tag: AccountFieldTag::CodeHash,
        value: U256::zero(),
        value_prev: U256::zero(),
    };
    let second = Rw::Account {
        rw_counter: 30,
        is_write: true,
        account_address: address!("0x2000000000000000000000000000000000000000"),
        field_tag: AccountFieldTag::CodeHash,
        value: U256::one(),
        value_prev: U256::one(),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_storage_key_upper() {
    let first = Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::zero(),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    };
    let second = Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::MAX - U256::one(),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_storage_key_lower() {
    let first = Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::zero(),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    };
    let second = Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::one(),
        value: U256::zero(),
        value_prev: U256::zero(),
        tx_id: 4,
        committed_value: U256::from(5),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_rw_counter() {
    let first = Rw::CallContext {
        rw_counter: 1,
        is_write: false,
        call_id: 1,
        field_tag: CallContextFieldTag::IsSuccess,
        value: U256::one(),
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: false,
        call_id: 1,
        field_tag: CallContextFieldTag::IsSuccess,
        value: U256::one(),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn lexicographic_ordering_previous_limb_differences_nonzero() {
    let rows = vec![
        Rw::TxRefund {
            rw_counter: 1,
            is_write: true,
            tx_id: 23,
            value: 20,
            value_prev: 40,
        },
        Rw::Account {
            rw_counter: 2,
            is_write: true,
            account_address: Address::zero(),
            field_tag: AccountFieldTag::Nonce,
            value: Word::zero(),
            value_prev: Word::zero(),
        },
    ];

    let overrides = HashMap::from([
        ((AdviceColumn::LimbIndexBit0, 1), Fr::one()),
        ((AdviceColumn::LimbIndexBit1, 1), Fr::one()),
        ((AdviceColumn::LimbIndexBit2, 1), Fr::one()),
        ((AdviceColumn::LimbIndexBit3, 1), Fr::one()),
        ((AdviceColumn::LimbIndexBit4, 1), Fr::one()),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(
        result,
        "limb differences before first_different_limb are all 0",
    );
}

#[test]
#[ignore = "read consistency constraint not implemented"]
fn read_inconsistency() {
    let rows = vec![
        Rw::Memory {
            rw_counter: 10,
            is_write: false,
            call_id: 1,
            memory_address: 10,
            byte: 0,
        },
        Rw::Memory {
            rw_counter: 40,
            is_write: false,
            call_id: 1,
            memory_address: 10,
            byte: 200,
        },
    ];

    assert_error_matches(verify(rows), "read consistency");
}

#[test]
#[ignore = "fix and re-enable once BinaryNumberChip is used for LexicographicOrderingChip"]
fn invalid_start_rw_counter() {
    let rows = vec![Rw::Start { rw_counter: 10 }];
    let overrides = HashMap::from([
        ((AdviceColumn::RwCounter, 0), Fr::from(2)),
        ((AdviceColumn::RwCounterLimb0, 0), Fr::from(2)),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "rw_counter is 0 for Start");
}

#[test]
fn all_padding() {
    assert_eq!(
        prover(vec![], HashMap::new()).verify_at_rows(0..100, 0..100),
        Ok(())
    );
}

#[test]
fn skipped_start_rw_counter() {
    let overrides = HashMap::from([
        (
            (AdviceColumn::RwCounter, -1),
            // The original assignment is 1 << 16.
            Fr::from((1 << 16) + 1),
        ),
        ((AdviceColumn::RwCounterLimb0, -1), Fr::one()),
    ]);

    let result = prover(vec![], overrides).verify_at_rows(N_ROWS - 1..N_ROWS, N_ROWS - 1..N_ROWS);
    assert_error_matches(result, "rw_counter increases by 1 for every non-first row");
}

#[test]
fn invalid_memory_address() {
    let rows = vec![Rw::Memory {
        rw_counter: 1,
        is_write: true,
        call_id: 1,
        memory_address: 1u64 << 32,
        byte: 12,
    }];

    assert_error_matches(verify(rows), "memory address fits into 2 limbs");
}

#[test]
fn first_memory_read_nonzero() {
    let rows = vec![Rw::Memory {
        rw_counter: 1,
        is_write: false,
        call_id: 1,
        memory_address: 10,
        byte: 200,
    }];

    assert_error_matches(verify(rows), "read from a fresh key is 0");
}

#[test]
fn invalid_memory_value() {
    let rows = vec![Rw::Memory {
        rw_counter: 1,
        is_write: true,
        call_id: 1,
        memory_address: 10,
        byte: 0,
    }];
    let overrides = HashMap::from([((AdviceColumn::Value, 0), Fr::from(256))]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "memory value is a byte");
}

#[test]
fn stack_read_before_write() {
    let rows = vec![Rw::Stack {
        rw_counter: 9,
        is_write: false,
        call_id: 3,
        stack_pointer: 200,
        value: U256::from(10),
    }];

    assert_error_matches(verify(rows), "first access to new stack address is a write");
}

#[test]
fn invalid_stack_address() {
    let rows = vec![Rw::Stack {
        rw_counter: 9,
        is_write: true,
        call_id: 3,
        stack_pointer: 3000,
        value: U256::from(10),
    }];

    assert_error_matches(verify(rows), "stack address fits into 10 bits");
}

#[test]
fn invalid_stack_address_change() {
    let rows = vec![
        Rw::Stack {
            rw_counter: 9,
            is_write: true,
            call_id: 3,
            stack_pointer: 100,
            value: U256::from(10),
        },
        Rw::Stack {
            rw_counter: 13,
            is_write: true,
            call_id: 3,
            stack_pointer: 102,
            value: U256::from(20),
        },
    ];

    assert_error_matches(
        verify(rows),
        "if previous row is also Stack with unchanged call id, address change is 0 or 1",
    );
}

#[test]
fn invalid_tags() {
    let first_row_offset = -isize::try_from(N_ROWS).unwrap();
    let tags: BTreeSet<usize> = RwTableTag::iter().map(|x| x as usize).collect();
    for i in 0..16 {
        if tags.contains(&i) {
            continue;
        }
        let bits: [Fr; 4] = i
            .as_bits()
            .map(|bit| if bit { Fr::one() } else { Fr::zero() });
        let overrides = HashMap::from([
            ((AdviceColumn::TagBit0, first_row_offset), bits[0]),
            ((AdviceColumn::TagBit1, first_row_offset), bits[1]),
            ((AdviceColumn::TagBit2, first_row_offset), bits[2]),
            ((AdviceColumn::TagBit3, first_row_offset), bits[3]),
        ]);

        let result = prover(vec![], overrides).verify_at_rows(0..1, 0..1);

        assert_error_matches(result, "binary number value in range");
    }
}

fn prover(rows: Vec<Rw>, overrides: HashMap<(AdviceColumn, isize), Fr>) -> MockProver<Fr> {
    let randomness = Fr::rand();
    let circuit = StateCircuit::<Fr, N_ROWS> {
        randomness,
        rows,
        overrides,
    };
    let power_of_randomness = circuit.instance();

    MockProver::<Fr>::run(17, &circuit, power_of_randomness).unwrap()
}

fn verify(rows: Vec<Rw>) -> Result<(), Vec<VerifyFailure>> {
    let used_rows = rows.len();
    prover(rows, HashMap::new())
        .verify_at_rows(N_ROWS - used_rows..N_ROWS, N_ROWS - used_rows..N_ROWS)
}

fn verify_with_overrides(
    rows: Vec<Rw>,
    overrides: HashMap<(AdviceColumn, isize), Fr>,
) -> Result<(), Vec<VerifyFailure>> {
    // Sanity check that the original RwTable without overrides is valid.
    assert_eq!(verify(rows.clone()), Ok(()));

    let n_active_rows = rows.len();
    prover(rows, overrides).verify_at_rows(
        N_ROWS - n_active_rows..N_ROWS,
        N_ROWS - n_active_rows..N_ROWS,
    )
}

fn assert_error_matches(result: Result<(), Vec<VerifyFailure>>, name: &str) {
    let errors = result.err().expect("result is not an error");
    assert_eq!(errors.len(), 1, "{:?}", errors);
    match &errors[0] {
        VerifyFailure::ConstraintNotSatisfied { constraint, .. } => {
            // fields of halo2_proofs::dev::metadata::Constraint aren't public, so we have
            // to match off of its format string.
            let constraint = format!("{}", constraint);
            if !constraint.contains(name) {
                panic!("{} does not contain {}", constraint, name);
            }
        }
        VerifyFailure::Lookup {
            name: lookup_name, ..
        } => {
            assert_eq!(lookup_name, &name)
        }
        VerifyFailure::CellNotAssigned { .. } => panic!(),
        VerifyFailure::ConstraintPoisoned { .. } => panic!(),
        VerifyFailure::Permutation { .. } => panic!(),
    }
}
