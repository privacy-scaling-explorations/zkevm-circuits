use bus_mapping::circuit_input_builder::BuilderClient;
use bus_mapping::rpc::GethClient;
use ethers_providers::Http;
use halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr},
    plonk::*,
    poly::kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::ProverSHPLONK,
    },
    transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer},
};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::str::FromStr;
use strum::IntoEnumIterator;
use zkevm_circuits::evm_circuit::{
    table::FixedTableTag, test::TestCircuit, witness::block_convert,
};
use zkevm_circuits::state_circuit::StateCircuit;

use crate::structs::Proofs;

type Scheme = KZGCommitmentScheme<Bn256>;

/// Gathers debug trace(s) from `rpc_url` for block `block_num` with `params`
/// created via the `gen_params` tool.
/// Expects a go-ethereum node with debug & archive capabilities on `rpc_url`.
pub async fn compute_proof(
    params: &ParamsKZG<Bn256>,
    block_num: &u64,
    rpc_url: &str,
) -> Result<Proofs, Box<dyn std::error::Error>> {
    // request & build the inputs for the circuits
    let url = Http::from_str(rpc_url)?;
    let geth_client = GethClient::new(url);
    let builder = BuilderClient::new(geth_client).await?;
    let builder = builder.gen_inputs(*block_num).await?;

    // TODO: only {evm,state}_proof are implemented right now
    let evm_proof;
    let state_proof;
    let block = block_convert(&builder.block, &builder.code_db);
    {
        // generate evm_circuit proof
        let circuit = TestCircuit::<Fr>::new(block.clone(), FixedTableTag::iter().collect());

        // TODO: can this be pre-generated to a file?
        // related
        // https://github.com/zcash/halo2/issues/443
        // https://github.com/zcash/halo2/issues/449
        let vk = keygen_vk::<Scheme, _>(params, &circuit)?;
        let pk = keygen_pk::<Scheme, _>(params, vk, &circuit)?;

        // Create randomness
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof::<Scheme, ProverSHPLONK<_>, _, _, _, _>(
            params,
            &pk,
            &[circuit],
            &[],
            rng,
            &mut transcript,
        )?;
        evm_proof = transcript.finalize();
    }

    {
        // generate state_circuit proof
        const N_ROWS: usize = 1 << 16;
        let circuit = StateCircuit::<Fr, N_ROWS>::new(block.randomness, block.rws);

        // TODO: same quest like in the first scope
        let vk = keygen_vk::<Scheme, _>(params, &circuit)?;
        let pk = keygen_pk::<Scheme, _>(params, vk, &circuit)?;

        // Create randomness
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        let instance = circuit.instance();
        let instance = instance.iter().map(|v| v.as_slice()).collect::<Vec<_>>();
        create_proof::<Scheme, ProverSHPLONK<_>, _, _, _, _>(
            params,
            &pk,
            &[circuit],
            &[instance.as_slice()],
            rng,
            &mut transcript,
        )?;
        state_proof = transcript.finalize();
    }

    let ret = Proofs {
        evm_proof: evm_proof.into(),
        state_proof: state_proof.into(),
    };

    Ok(ret)
}
