pub use super::{dev::*, *};
use crate::{
    table::{AccountFieldTag, CallContextFieldTag, TxLogFieldTag, TxReceiptFieldTag},
    util::{unusable_rows, SubCircuit},
    witness::{chunk::*, MptUpdates, Rw, RwMap},
};
use bus_mapping::operation::{
    MemoryOp, Operation, OperationContainer, RWCounter, StackOp, StorageOp, RW,
};
use eth_types::{
    address,
    evm_types::{MemoryAddress, StackAddress},
    Address, ToAddress, Word, U256,
};
use gadgets::binary_number::AsBits;
use halo2_proofs::{
    arithmetic::Field as Halo2Field,
    dev::{MockProver, VerifyFailure},
    halo2curves::bn256::{Bn256, Fr},
    plonk::{keygen_vk, Circuit, ConstraintSystem},
    poly::kzg::commitment::ParamsKZG,
};
use rand::SeedableRng;
use std::collections::{BTreeSet, HashMap};
use strum::IntoEnumIterator;

const N_ROWS: usize = 1 << 16;

#[test]
fn state_circuit_unusable_rows() {
    assert_eq!(
        StateCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, StateCircuit::<Fr>>(()),
    )
}

fn new_chunk_from_rw_map<F: Field>(rws: &RwMap, padding_start_rw: Option<Rw>) -> Chunk<F> {
    let (alpha, gamma) = get_permutation_randomness();
    let mut chunk = Chunk {
        by_address_rws: rws.clone(),
        ..Default::default()
    };

    let rw_fingerprints = get_permutation_fingerprint_of_rwmap(
        &chunk.by_address_rws,
        chunk.fixed_param.max_rws,
        alpha,
        gamma,
        F::from(1),
        false,
        padding_start_rw,
    );
    chunk.by_address_rw_fingerprints = rw_fingerprints;
    chunk
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
    let chunk = new_chunk_from_rw_map(&rw_map, None);

    let circuit = StateCircuit::<Fr>::new(&chunk);
    let instance = circuit.instance();

    let prover = MockProver::<Fr>::run(19, &circuit, instance).unwrap();
    let verify_result = prover.verify();
    assert_eq!(verify_result, Ok(()));
}

#[test]
fn degree() {
    let mut meta = ConstraintSystem::<Fr>::default();
    StateCircuit::<Fr>::configure(&mut meta);
    assert_eq!(meta.degree(), 10);
}

#[test]
fn verifying_key_independent_of_rw_length() {
    let params = ParamsKZG::<Bn256>::setup(17, rand_chacha::ChaCha20Rng::seed_from_u64(2));
    let mut chunk = Chunk::default();

    let no_rows = StateCircuit::<Fr>::new(&chunk);

    chunk = new_chunk_from_rw_map(
        &RwMap::from(&OperationContainer {
            memory: vec![Operation::new(
                RWCounter::from(1),
                RWCounter::from(1),
                RW::WRITE,
                MemoryOp::new(1, MemoryAddress::from(0), 32),
            )],
            ..Default::default()
        }),
        None,
    );
    let one_row = StateCircuit::<Fr>::new(&chunk);

    let vk_no_rows = keygen_vk(&params, &no_rows).unwrap();
    let vk_one_rows = keygen_vk(&params, &one_row).unwrap();
    assert_eq!(
        vk_no_rows.fixed_commitments(),
        vk_one_rows.fixed_commitments()
    );
    assert_eq!(
        vk_no_rows.permutation().commitments(),
        vk_one_rows.permutation().commitments()
    );
}

#[test]
fn state_circuit_simple_2() {
    let memory_op_0 = Operation::new(
        RWCounter::from(12),
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let memory_op_1 = Operation::new(
        RWCounter::from(24),
        RWCounter::from(24),
        RW::READ,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );

    let memory_op_2 = Operation::new(
        RWCounter::from(17),
        RWCounter::from(17),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(1), 32),
    );
    let memory_op_3 = Operation::new(
        RWCounter::from(87),
        RWCounter::from(87),
        RW::READ,
        MemoryOp::new(1, MemoryAddress::from(1), 32),
    );

    let stack_op_0 = Operation::new(
        RWCounter::from(17),
        RWCounter::from(17),
        RW::WRITE,
        StackOp::new(1, StackAddress::from(1), Word::from(32)),
    );
    let stack_op_1 = Operation::new(
        RWCounter::from(87),
        RWCounter::from(87),
        RW::READ,
        StackOp::new(1, StackAddress::from(1), Word::from(32)),
    );

    let storage_op_0 = Operation::new(
        RWCounter::from(0),
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
        RWCounter::from(18),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::from(32),
            1usize,
            Word::zero(),
        ),
    );
    let storage_op_2 = Operation::new(
        RWCounter::from(19),
        RWCounter::from(19),
        RW::WRITE,
        StorageOp::new(
            U256::from(100).to_address(),
            Word::from(0x40),
            Word::from(32),
            Word::from(32),
            1usize,
            Word::zero(),
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
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let memory_op_1 = Operation::new(
        RWCounter::from(13),
        RWCounter::from(13),
        RW::READ,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let storage_op_2 = Operation::new(
        RWCounter::from(19),
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
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let storage_op = Operation::new(
        RWCounter::from(19),
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
        RWCounter::from(12),
        RW::WRITE,
        MemoryOp::new(1, MemoryAddress::from(0), 32),
    );
    let memory_op_1 = Operation::new(
        RWCounter::from(13),
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
fn tx_log_ok() {
    let rows = vec![
        Rw::Stack {
            rw_counter: 1,
            is_write: true,
            call_id: 1,
            stack_pointer: 1023,
            value: U256::from(394500u64),
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 3,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 0usize,
            value: U256::one(),
        },
        Rw::TxLog {
            rw_counter: 4,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 1usize,
            value: U256::from(2u64),
        },
        Rw::TxLog {
            rw_counter: 5,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Data,
            index: 0usize,
            value: U256::from(3u64),
        },
        Rw::TxLog {
            rw_counter: 6,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Data,
            index: 1usize,
            value: U256::from(3u64),
        },
    ];

    assert_eq!(verify(rows), Ok(()));
}

#[test]
fn tx_log_bad() {
    // is_write is false
    let rows = vec![Rw::TxLog {
        rw_counter: 2,
        is_write: false,
        tx_id: 1,
        log_id: 1,
        field_tag: TxLogFieldTag::Address,
        index: 0usize,
        value: U256::zero(),
    }];

    assert_error_matches(verify(rows), "is_write is always true for TxLog");
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
    let overrides = HashMap::from([((AdviceColumn::AddressLimb0, 0), Fr::ZERO)]);

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
        ((AdviceColumn::AddressLimb1, 0), Fr::ZERO),
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
        value: U256::from(34),
        value_prev: U256::from(34),
        tx_id: 4,
        committed_value: U256::from(34),
    }];
    let overrides = HashMap::from([((AdviceColumn::StorageKeyLimb0, 0), Fr::ONE)]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "mpi value matches claimed limbs");
}

#[test]
fn is_write_nonbinary() {
    let rows = vec![Rw::CallContext {
        rw_counter: 1,
        is_write: false,
        call_id: 0,
        field_tag: CallContextFieldTag::TxId,
        value: U256::zero(),
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
        value: U256::zero(),
    };

    assert_eq!(verify(vec![first, second]), Ok(()));
    assert_error_matches(verify(vec![second, first]), "limb_difference fits into u16");
}

#[test]
fn nonlexicographic_order_field_tag() {
    let first = Rw::CallContext {
        rw_counter: 5,
        is_write: true,
        call_id: 0,
        field_tag: CallContextFieldTag::RwCounterEndOfReversion,
        value: U256::from(100),
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: true,
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
        is_write: true,
        call_id: 0,
        field_tag: CallContextFieldTag::RwCounterEndOfReversion,
        value: U256::from(100),
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: true,
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
        value: U256::from(800),
        value_prev: U256::from(800),
        tx_id: 4,
        committed_value: U256::from(800),
    };
    let second = Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::MAX - U256::one(),
        value: U256::from(300),
        value_prev: U256::from(300),
        tx_id: 4,
        committed_value: U256::from(300),
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
        value: U256::from(200),
        value_prev: U256::from(200),
        tx_id: 4,
        committed_value: U256::from(200),
    };
    let second = Rw::AccountStorage {
        rw_counter: 1,
        is_write: false,
        account_address: Address::default(),
        storage_key: U256::one(),
        value: U256::from(200),
        value_prev: U256::from(200),
        tx_id: 4,
        committed_value: U256::from(200),
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
        value: U256::zero(),
    };
    let second = Rw::CallContext {
        rw_counter: 2,
        is_write: false,
        call_id: 1,
        field_tag: CallContextFieldTag::IsSuccess,
        value: U256::zero(),
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
            value_prev: 0,
        },
        Rw::Account {
            rw_counter: 2,
            is_write: true,
            account_address: address!("0x0000000000000000000000000000000000000001"),
            field_tag: AccountFieldTag::Nonce,
            value: Word::zero(),
            value_prev: Word::zero(),
        },
    ];

    // overriding first_different_limb to be in AddressLimb0 instead of Tag. The
    // limb difference between the two rows here is still 1, so no additional
    // overrides are needed.
    let overrides = HashMap::from([
        ((AdviceColumn::LimbIndexBit1, 1), Fr::ONE),
        ((AdviceColumn::LimbIndexBit2, 1), Fr::ONE),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(
        result,
        "limb differences before first_different_limb are all 0",
    );
}

#[test]
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

    assert_error_matches(verify(rows), "non-first access reads don't change value");
}

#[test]
fn all_padding() {
    assert_eq!(
        prover(vec![], HashMap::new()).verify_at_rows(0..100, 0..100),
        Ok(())
    );
}

#[test]
fn invalid_padding_rw_counter_change() {
    let overrides = HashMap::from([
        (
            (AdviceColumn::RwCounter, 0),
            // The original assignment is 1 << 16.
            Fr::from((1 << 16) + 1),
        ),
        ((AdviceColumn::RwCounterLimb0, 0), Fr::ONE),
    ]);

    let result = prover(vec![], overrides).verify_at_rows(2..3, 2..3);
    assert_error_matches(
        result,
        "if previous row is also Padding. rw counter change is 0 or 1",
    );
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
fn bad_initial_memory_value() {
    let rows = vec![Rw::Memory {
        rw_counter: 1,
        is_write: true,
        call_id: 1,
        memory_address: 10,
        byte: 0,
    }];

    let v = Fr::from(200);
    let overrides = HashMap::from([
        ((AdviceColumn::ValueLo, 0), v),
        ((AdviceColumn::ValueHi, 0), Fr::ZERO),
        ((AdviceColumn::ValuePrevLo, 0), v),
        ((AdviceColumn::ValuePrevHi, 0), Fr::ZERO),
        ((AdviceColumn::IsZero, 0), Fr::ZERO),
        ((AdviceColumn::NonEmptyWitness, 0), v.invert().unwrap()),
        ((AdviceColumn::InitialValueLo, 0), v),
        ((AdviceColumn::InitialValueHi, 0), Fr::ZERO),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "initial Memory value is 0");
}

#[test]
fn invalid_memory_value() {
    let rows = vec![Rw::Memory {
        rw_counter: 1,
        is_write: true,
        call_id: 1,
        memory_address: 10,
        byte: 1,
    }];
    let v = Fr::from(256);
    let overrides = HashMap::from([
        ((AdviceColumn::ValueHi, 0), Fr::ZERO),
        ((AdviceColumn::ValueLo, 0), v),
        ((AdviceColumn::NonEmptyWitness, 0), v.invert().unwrap()),
    ]);

    let result = verify_with_overrides(rows, overrides);

    assert_error_matches(result, "memory value is a byte (lo is u8)");
}

#[test]
fn stack_read_before_write() {
    let rows = vec![Rw::Stack {
        rw_counter: 9,
        is_write: false,
        call_id: 3,
        stack_pointer: 200,
        value: U256::zero(),
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
    let first_row_offset = 0;
    let tags: BTreeSet<usize> = Target::iter().map(|x| x as usize).collect();
    for i in 0..16 {
        if tags.contains(&i) {
            continue;
        }
        let bits: [Fr; 4] = i.as_bits().map(|bit| if bit { Fr::ONE } else { Fr::ZERO });
        let overrides = HashMap::from([
            ((AdviceColumn::TagBit0, first_row_offset), bits[0]),
            ((AdviceColumn::TagBit1, first_row_offset), bits[1]),
            ((AdviceColumn::TagBit2, first_row_offset), bits[2]),
            ((AdviceColumn::TagBit3, first_row_offset), bits[3]),
            ((AdviceColumn::Tag, first_row_offset), Fr::from(i as u64)),
        ]);

        // offset 0 is padding
        let result = prover(vec![], overrides).verify_at_rows(1..2, 1..2);
        assert_error_matches(result, "binary number value in range");
    }
}

#[test]
fn bad_initial_stack_value() {
    let rows = vec![Rw::Stack {
        rw_counter: 1,
        is_write: true,
        call_id: 1,
        stack_pointer: 10,
        value: Word::from(10),
    }];

    let overrides = HashMap::from([
        ((AdviceColumn::InitialValueHi, 0), Fr::ZERO),
        ((AdviceColumn::InitialValueLo, 0), Fr::from(10)),
        ((AdviceColumn::ValuePrevHi, 0), Fr::ZERO),
        ((AdviceColumn::ValuePrevLo, 0), Fr::from(10)),
    ]);

    assert_error_matches(
        verify_with_overrides(rows, overrides),
        "initial Stack value is 0",
    );
}

#[test]
fn bad_initial_tx_access_list_account_value() {
    let rows = vec![Rw::TxAccessListAccount {
        rw_counter: 1,
        is_write: true,
        tx_id: 1,
        account_address: address!("0x0000000000000000000000000000000004356002"),
        is_warm: true,
        is_warm_prev: false,
    }];

    let overrides = HashMap::from([
        ((AdviceColumn::InitialValueHi, 0), Fr::ZERO),
        ((AdviceColumn::InitialValueLo, 0), Fr::from(1)),
        ((AdviceColumn::ValuePrevHi, 0), Fr::ZERO),
        ((AdviceColumn::ValuePrevLo, 0), Fr::from(1)),
    ]);

    assert_error_matches(
        verify_with_overrides(rows, overrides),
        "initial TxAccessListAccount value is false",
    );
}

#[test]
fn bad_initial_tx_refund_value() {
    let rows = vec![Rw::TxRefund {
        rw_counter: 1,
        is_write: false,
        tx_id: 1,
        value: 0,
        value_prev: 0,
    }];
    let v = Fr::from(10);
    let overrides = HashMap::from([
        ((AdviceColumn::IsWrite, 0), Fr::from(1)),
        ((AdviceColumn::ValueHi, 0), Fr::ZERO),
        ((AdviceColumn::ValueLo, 0), v),
        ((AdviceColumn::ValuePrevHi, 0), Fr::ZERO),
        ((AdviceColumn::ValuePrevLo, 0), v),
        ((AdviceColumn::IsZero, 0), Fr::ZERO),
        ((AdviceColumn::NonEmptyWitness, 0), v.invert().unwrap()),
        ((AdviceColumn::InitialValueHi, 0), Fr::ZERO),
        ((AdviceColumn::InitialValueLo, 0), v),
    ]);

    assert_error_matches(
        verify_with_overrides(rows, overrides),
        "initial TxRefund value is 0",
    );
}

#[test]
fn bad_initial_tx_log_value() {
    let rows = vec![Rw::TxLog {
        rw_counter: 1,
        is_write: true,
        tx_id: 800,
        log_id: 4,
        field_tag: TxLogFieldTag::Topic,
        index: 2,
        value: U256::from(300),
    }];

    let overrides = HashMap::from([
        ((AdviceColumn::InitialValueHi, 0), Fr::ZERO),
        ((AdviceColumn::InitialValueLo, 0), Fr::from(10)),
        ((AdviceColumn::ValuePrevHi, 0), Fr::ZERO),
        ((AdviceColumn::ValuePrevLo, 0), Fr::from(10)),
    ]);

    assert_error_matches(
        verify_with_overrides(rows, overrides),
        "initial TxLog value is 0",
    );
}

#[test]
fn variadic_size_check() {
    let mut rows = vec![
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
    // let rw_map: RwMap = rows.clone().into();
    let circuit = StateCircuit::new(&new_chunk_from_rw_map(&RwMap::from(rows.clone()), None));
    let power_of_randomness = circuit.instance();
    let prover1 = MockProver::<Fr>::run(17, &circuit, power_of_randomness).unwrap();

    rows.extend_from_slice(&[
        Rw::Stack {
            rw_counter: 26,
            is_write: true,
            call_id: 1,
            stack_pointer: 1021,
            value: U256::from(394511u64),
        },
        Rw::Stack {
            rw_counter: 27,
            is_write: false,
            call_id: 1,
            stack_pointer: 1021,
            value: U256::from(394511u64),
        },
    ]);

    let circuit = StateCircuit::new(&new_chunk_from_rw_map(&rows.into(), None));
    let power_of_randomness = circuit.instance();
    let prover2 = MockProver::<Fr>::run(17, &circuit, power_of_randomness).unwrap();

    assert_eq!(prover1.fixed(), prover2.fixed());
    assert_eq!(prover1.permutation(), prover2.permutation());
}

#[test]
#[ignore = "TxReceipt constraints not yet implemented"]
fn bad_initial_tx_receipt_value() {
    let rows = vec![Rw::TxReceipt {
        rw_counter: 1,
        is_write: false,
        tx_id: 3421,
        field_tag: TxReceiptFieldTag::CumulativeGasUsed,
        value: 0,
    }];

    let overrides = HashMap::from([
        ((AdviceColumn::ValueHi, 0), Fr::ZERO),
        ((AdviceColumn::ValueLo, 0), Fr::from(1900)),
        ((AdviceColumn::InitialValueHi, 0), Fr::ZERO),
        ((AdviceColumn::InitialValueLo, 0), Fr::from(1900)),
    ]);

    assert_error_matches(
        verify_with_overrides(rows, overrides),
        "initial TxReceipt value is 0",
    );
}

fn prover(rows: Vec<Rw>, overrides: HashMap<(AdviceColumn, isize), Fr>) -> MockProver<Fr> {
    // permu_next_continuous_fingerprint and rows override for negative-test
    #[allow(unused_assignments, unused_mut)]
    let (rw_rows, _) = RwMap::table_assignments_padding(&rows, N_ROWS, None);
    let rw_rows: Vec<witness::RwRow<Value<Fr>>> =
        rw_overrides_skip_first_padding(&rw_rows, &overrides);
    let rwtable_fingerprints =
        get_permutation_fingerprint_of_rwrowvec(&rw_rows, N_ROWS, Fr::ONE, Fr::ONE, Fr::ONE, None);
    let row_padding_and_overridess = rw_rows.to2dvec();

    let updates = MptUpdates::mock_from(&rows);
    let circuit = StateCircuit::<Fr> {
        rows,
        row_padding_and_overrides: row_padding_and_overridess,
        updates,
        overrides,
        n_rows: N_ROWS,
        permu_alpha: Fr::from(1),
        permu_gamma: Fr::from(1),
        rw_fingerprints: rwtable_fingerprints,
        prev_chunk_last_rw: None,
        _marker: std::marker::PhantomData,
    };
    let instance = circuit.instance();

    MockProver::<Fr>::run(17, &circuit, instance).unwrap()
}

fn verify(rows: Vec<Rw>) -> Result<(), Vec<VerifyFailure>> {
    let used_rows = rows.len();
    prover(rows, HashMap::new()).verify_at_rows(1..used_rows + 1, 1..used_rows + 1)
}

fn verify_with_overrides(
    rows: Vec<Rw>,
    overrides: HashMap<(AdviceColumn, isize), Fr>,
) -> Result<(), Vec<VerifyFailure>> {
    // Sanity check that the original RwTable without overrides is valid.
    assert_eq!(verify(rows.clone()), Ok(()));

    let n_active_rows = rows.len();
    prover(rows, overrides).verify_at_rows(1..n_active_rows + 1, 1..n_active_rows + 1)
}

fn assert_error_matches(result: Result<(), Vec<VerifyFailure>>, name: &str) {
    let errors = result.expect_err("result is not an error");
    errors
        .iter()
        .find(|err| match err {
            VerifyFailure::ConstraintNotSatisfied { constraint, .. } => {
                // fields of halo2_proofs::dev::metadata::Constraint aren't public, so we have
                // to match off of its format string.
                let constraint = format!("{}", constraint);
                constraint.contains(name)
            }
            VerifyFailure::Lookup {
                name: lookup_name, ..
            } => {
                assert_eq!(lookup_name, &name);
                true
            }
            VerifyFailure::CellNotAssigned { .. } => false,
            VerifyFailure::ConstraintPoisoned { .. } => false,
            VerifyFailure::Permutation { .. } => false,
            VerifyFailure::InstanceCellNotAssigned { .. } => false,
            VerifyFailure::Shuffle { .. } => false,
        })
        .unwrap_or_else(|| {
            panic!(
                "there is no constraints contain {}; err {:#?}",
                name, errors
            )
        });
}
