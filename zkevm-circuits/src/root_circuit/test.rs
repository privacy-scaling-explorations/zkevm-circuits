use std::iter;

use crate::{
    copy_circuit::{CopyCircuit, ExternalData},
    root_circuit::{
        aggregation::test::SnarkOwned, compile, Config, Gwc, PoseidonTranscript, RootCircuit,
        SnarkWitness, TestAggregationCircuit, UserChallenge,
    },
    super_circuit::{test::block_1tx, SuperCircuit},
    table::{self, AccountFieldTag, LookupTable, TxLogFieldTag},
    util::{self, SubCircuit},
    witness::{block_convert, chunk_convert, Rw, RwRow},
};
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, FixedCParams},
    mock::BlockData,
};
use eth_types::{address, bytecode, geth_types::GethData, Address, Field, Word, U256};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::{bn256::Bn256, pairing::Engine},
    plonk::{create_proof, keygen_pk, keygen_vk, Circuit, ConstraintSystem, Error},
    poly::{
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverGWC,
        },
        Rotation,
    },
};
use itertools::Itertools;
use mock::TestContext;
use rand::rngs::OsRng;
use table::RwTable;
use util::{word::WordLoHi, Challenges};

fn gen_tx_log_data() -> CircuitInputBuilder<FixedCParams> {
    let code = bytecode! {
        PUSH32(200)         // value
        PUSH32(0)           // offset
        MSTORE
        PUSH32(Word::MAX)   // topic
        PUSH1(32)           // length
        PUSH1(0)            // offset
        LOG1
        STOP
    };
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    // Needs default params for variadic check

    BlockData::new_from_geth_data_with_params(block.clone(), FixedCParams::default())
        .new_circuit_input_builder()
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap()
}

struct RwTableCircuit<'a> {
    rws: &'a [Rw],
    n_rows: usize,
    prev_chunk_last_rw: Option<Rw>,
}

impl<'a> RwTableCircuit<'a> {
    #[allow(dead_code)]
    pub(crate) fn new(rws: &'a [Rw], n_rows: usize, prev_chunk_last_rw: Option<Rw>) -> Self {
        Self {
            rws,
            n_rows,
            prev_chunk_last_rw,
        }
    }
}

#[derive(Clone)]
pub(crate) struct RwTableCircuitConfig {
    pub rw_table: RwTable,
}

impl RwTableCircuitConfig {}

impl<'a, F: Field> Circuit<F> for RwTableCircuit<'a> {
    type Config = RwTableCircuitConfig;

    type FloorPlanner = SimpleFloorPlanner;

    type Params = ();

    fn without_witnesses(&self) -> Self {
        todo!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let rw_table = RwTable::construct(meta);

        meta.create_gate("zero gate", |meta| {
            let dummy = meta.query_advice(rw_table.address, Rotation::cur());

            vec![dummy.clone() - dummy]
        });
        RwTableCircuitConfig { rw_table }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "XXXX",
            |mut region| {
                let _ = config.rw_table.load_with_region(
                    &mut region,
                    self.rws,
                    self.n_rows,
                    self.prev_chunk_last_rw,
                );
                // avoid empty column cause commitment value as identity point
                config.rw_table.assign(
                    &mut region,
                    0,
                    &RwRow {
                        rw_counter: Value::known(F::ONE),
                        is_write: Value::known(F::ONE),
                        tag: Value::known(F::ONE),
                        id: Value::known(F::ONE),
                        address: Value::known(F::ONE),
                        field_tag: Value::known(F::ONE),
                        storage_key: WordLoHi::new([F::ONE, F::ONE]).into_value(),
                        value: WordLoHi::new([F::ONE, F::ONE]).into_value(),
                        value_prev: WordLoHi::new([F::ONE, F::ONE]).into_value(),
                        init_val: WordLoHi::new([F::ONE, F::ONE]).into_value(),
                    },
                )
            },
        )?;
        Ok(())
    }
}

#[test]
fn test_user_challenge_aggregation() {
    let k = 12;
    let rows = vec![
        Rw::Stack {
            rw_counter: 9,
            is_write: true,
            call_id: 3,
            stack_pointer: 100,
            value: U256::MAX - 1,
        },
        Rw::Stack {
            rw_counter: 13,
            is_write: true,
            call_id: 3,
            stack_pointer: 102,
            value: U256::MAX - 1,
        },
        Rw::Stack {
            rw_counter: 1,
            is_write: true,
            call_id: 1,
            stack_pointer: 1023,
            value: U256::MAX - 1,
        },
        Rw::TxLog {
            rw_counter: 2,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Address,
            index: 0usize,
            value: U256::MAX - 1,
        },
        Rw::TxLog {
            rw_counter: 3,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 0usize,
            value: U256::MAX - 1,
        },
        Rw::TxLog {
            rw_counter: 4,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Topic,
            index: 1usize,
            value: U256::MAX - 1,
        },
        Rw::TxLog {
            rw_counter: 5,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Data,
            index: 10usize,
            value: U256::MAX - 1,
        },
        Rw::TxLog {
            rw_counter: 6,
            is_write: true,
            tx_id: 1,
            log_id: 1,
            field_tag: TxLogFieldTag::Data,
            index: 1usize,
            value: U256::MAX - 1,
        },
        Rw::Account {
            rw_counter: 1,
            is_write: false,
            account_address: address!("0x000000000000000000000000000000000cafe002"),
            field_tag: AccountFieldTag::CodeHash,
            value: U256::MAX - 1,
            value_prev: U256::MAX - 1,
        },
        Rw::AccountStorage {
            rw_counter: 1,
            is_write: false,
            account_address: Address::default(),
            storage_key: U256::MAX - 1,
            value: U256::MAX - 1,
            value_prev: U256::MAX - 1,
            tx_id: 4,
            committed_value: U256::MAX - 1,
        },
    ];

    let builder = gen_tx_log_data();
    let block = block_convert::<<Bn256 as Engine>::Fr>(&builder).unwrap();
    let chunk = chunk_convert::<<Bn256 as Engine>::Fr>(&block, &builder)
        .unwrap()
        .remove(0);
    let chunked_copy_events = block.copy_events.get(0..1).unwrap_or_default();
    // let circuits = iter::repeat_with(|| {
    //     CopyCircuit::<<Bn256 as Engine>::Fr>::new_with_external_data(
    //         chunked_copy_events.to_owned(),
    //         chunk.fixed_param.max_copy_rows,
    //         ExternalData {
    //             max_txs: chunk.fixed_param.max_txs,
    //             max_calldata: chunk.fixed_param.max_calldata,
    //             txs: block.txs.clone(),
    //             max_rws: chunk.fixed_param.max_rws,
    //             rws: chunk.chrono_rws.clone(),
    //             prev_chunk_last_rw: chunk.prev_chunk_last_chrono_rw,
    //             bytecodes: block.bytecodes.clone(),
    //         },
    //     )
    // })
    // .take(1)
    // .collect_vec();

    let circuits = iter::repeat_with(|| RwTableCircuit::new(&rows, rows.len() + 1, None))
        .take(1)
        .collect_vec();

    let mut cs = ConstraintSystem::<<Bn256 as Engine>::Fr>::default();
    // let (config, _) = CopyCircuit::configure_with_params(
    //     &mut cs,
    //     <CopyCircuit<_> as Circuit<<Bn256 as Engine>::Fr>>::params(&circuits[0]),
    // );
    let config = RwTableCircuit::configure_with_params(
        &mut cs,
        <RwTableCircuit as Circuit<<Bn256 as Engine>::Fr>>::params(&circuits[0]),
    );
    let rwtable_columns =
        <table::RwTable as LookupTable<<Bn256 as Engine>::Fr>>::columns(&config.rw_table);

    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    // let advice_commitments = get_rwtable_cols_commitment::<KZGCommitmentScheme<_>>(
    //     k.try_into().unwrap(),
    //     &rows,
    //     rows.len() + 1,
    //     &params,
    // );

    let pk = keygen_pk(
        &params,
        keygen_vk(&params, &circuits[0]).unwrap(),
        &circuits[0],
    )
    .unwrap();
    let protocol = compile(
        &params,
        pk.get_vk(),
        Config::kzg().with_num_instance(vec![0]),
    );
    // Create proof
    let proofs: Vec<Vec<u8>> = circuits
        .into_iter()
        .map(|circuit| {
            // Create proof
            let proof = {
                let mut transcript = PoseidonTranscript::new(Vec::new());
                create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                    &params,
                    &pk,
                    &[circuit],
                    &[&[]],
                    OsRng,
                    &mut transcript,
                )
                .unwrap();
                transcript.finalize()
            };
            proof
        })
        .collect();
    let user_challenge = UserChallenge {
        column_indexes: rwtable_columns,
        num_challenges: 1,
    };
    let snark_witnesses: Vec<_> = proofs
        .into_iter()
        .map(|proof| SnarkOwned::new(protocol.clone(), vec![vec![]], proof))
        .collect();
    let aggregation = TestAggregationCircuit::<Bn256, Gwc<_>>::new(
        &params,
        snark_witnesses.iter().map(SnarkOwned::as_snark),
        // Some((user_challenge, vec![<Bn256 as Engine>::Fr::from(1)])),
        None,
    )
    .unwrap();

    let instances = aggregation.instances();
    assert_eq!(
        MockProver::run(21, &aggregation, instances)
            .unwrap()
            .verify(),
        Ok(())
    );
}

#[ignore = "Due to high memory requirement"]
#[test]
fn test_root_circuit_multiple_chunk() {
    let (params, protocol, proofs, instances, rwtable_columns) = {
        // Preprocess
        const TEST_MOCK_RANDOMNESS: u64 = 0x100;
        let circuits_params = FixedCParams {
            total_chunks: 3,
            max_txs: 1,
            max_withdrawals: 5,
            max_calldata: 32,
            max_rws: 100,
            max_copy_rows: 256,
            max_exp_steps: 256,
            max_bytecode: 512,
            max_evm_rows: 1 << 12,
            max_keccak_rows: 0,
            max_vertical_circuit_rows: 0,
        };
        let (k, circuits, instances, _) =
            SuperCircuit::<_>::build(block_1tx(), circuits_params, TEST_MOCK_RANDOMNESS.into())
                .unwrap();
        assert!(!circuits.is_empty());
        assert!(circuits.len() == instances.len());

        // get chronological_rwtable and byaddr_rwtable columns index
        let mut cs = ConstraintSystem::default();
        let config = SuperCircuit::configure_with_params(&mut cs, circuits[0].params());
        let rwtable_columns = config.get_rwtable_columns();

        let params = ParamsKZG::<Bn256>::setup(k, OsRng);
        let pk = keygen_pk(
            &params,
            keygen_vk(&params, &circuits[0]).unwrap(),
            &circuits[0],
        )
        .unwrap();
        let protocol = compile(
            &params,
            pk.get_vk(),
            Config::kzg()
                .with_num_instance(instances[0].iter().map(|instance| instance.len()).collect()),
        );

        let proofs: Vec<Vec<u8>> = circuits
            .into_iter()
            .zip(instances.iter())
            .map(|(circuit, instance)| {
                // Create proof
                let proof = {
                    let mut transcript = PoseidonTranscript::new(Vec::new());
                    create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                        &params,
                        &pk,
                        &[circuit],
                        &[&instance.iter().map(Vec::as_slice).collect_vec()],
                        OsRng,
                        &mut transcript,
                    )
                    .unwrap();
                    transcript.finalize()
                };
                proof
            })
            .collect();
        (params, protocol, proofs, instances, rwtable_columns)
    };

    let user_challenge = UserChallenge {
        column_indexes: rwtable_columns,
        num_challenges: 2, // alpha, gamma
    };
    let snark_witnesses: Vec<_> = proofs
        .iter()
        .zip(instances.iter())
        .map(|(proof, instance)| {
            SnarkWitness::new(&protocol, Value::known(instance), Value::known(proof))
        })
        .collect();

    let root_circuit = RootCircuit::<Bn256, Gwc<_>>::new(
        &params,
        &protocol,
        snark_witnesses,
        Some(&user_challenge),
    )
    .unwrap();
    assert_eq!(
        MockProver::run(26, &root_circuit, root_circuit.instance())
            .unwrap()
            .verify(),
        Ok(())
    );
}
