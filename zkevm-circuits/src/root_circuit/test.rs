use crate::{
    root_circuit::{
        compile, Config, Gwc, PoseidonTranscript, RootCircuit, SnarkWitness, UserChallenge,
    },
    super_circuit::{test::block_1tx, SuperCircuit},
};
use bus_mapping::circuit_input_builder::FixedCParams;
use halo2_proofs::{
    circuit::Value,
    dev::MockProver,
    halo2curves::bn256::Bn256,
    plonk::{create_proof, keygen_pk, keygen_vk, Circuit, ConstraintSystem},
    poly::kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::ProverGWC,
    },
};
use itertools::Itertools;
use rand::rngs::OsRng;

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
