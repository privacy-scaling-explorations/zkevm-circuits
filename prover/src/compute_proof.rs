use bus_mapping::circuit_input_builder::BuilderClient;
use bus_mapping::rpc::GethClient;
use ethers_providers::Http;
use halo2_proofs::{
    pairing::{
        bn256::{Fr, G1Affine},
        group::ff::PrimeField,
    },
    plonk::*,
    poly::commitment::Params,
    transcript::{Blake2bWrite, Challenge255},
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
use crate::structs::Witness;

fn store_word_bytes(buf: &mut Vec<u8>, val: &[u8]) {
    let mut tmp: Vec<u8> = Vec::with_capacity(32);
    tmp.resize(32 - val.len(), 0);
    tmp.extend(val);

    buf.extend(tmp);
}

macro_rules! store_word {
    ($a:expr, $b:expr) => {
        let mut tmp: Vec<u8> = vec![0; 32];
        $b.to_big_endian(&mut tmp);
        $a.extend(tmp);
    };
}

/// Gathers debug trace(s) from `rpc_url` for block `block_num` and
/// generates a witness suitable for the L1 Verifier contract(s).
pub async fn compute_witness(
    block_num: &u64,
    rpc_url: &str,
) -> Result<Witness, Box<dyn std::error::Error>> {
    // request & build the inputs for the circuits
    let url = Http::from_str(rpc_url)?;
    let geth_client = GethClient::new(url);
    let builder = BuilderClient::new(geth_client).await?;
    let builder = builder.gen_inputs(*block_num).await?;

    let block = block_convert(&builder.block, &builder.code_db);
    let mut witness: Vec<u8> = Vec::new();

    // TODO:
    // some data is intentionally left out until the layout & contents
    // requirements are decided on.
    {
        // block
        store_word!(&mut witness, block.context.chain_id);
        store_word_bytes(&mut witness, block.context.coinbase.as_ref());
        store_word_bytes(&mut witness, &block.context.gas_limit.to_be_bytes());
        store_word!(&mut witness, block.context.number);
        store_word!(&mut witness, block.context.timestamp);
        store_word!(&mut witness, block.context.difficulty);
        store_word!(&mut witness, block.context.base_fee);
        // TODO: block_hash and history_hashes
    }

    {
        // transactions
        let iter = block.txs.iter();
        store_word_bytes(&mut witness, &iter.len().to_be_bytes());

        for tx in iter {
            // TODO: clarify which values are required
            store_word_bytes(&mut witness, &tx.nonce.to_be_bytes());
            store_word!(&mut witness, &tx.gas_price);
            store_word_bytes(&mut witness, &tx.gas.to_be_bytes());
            if tx.is_create {
                // set MSB
                let mut v = vec![0; 32];
                v[0] = 0x80;
                store_word_bytes(&mut witness, &v);
            } else {
                store_word_bytes(&mut witness, tx.caller_address.as_ref());
            }
            store_word!(&mut witness, tx.value);
            store_word_bytes(&mut witness, &tx.call_data_length.to_be_bytes());
            // expand each byte to a full evm word (o.O)
            for byte in tx.call_data.iter() {
                store_word_bytes(&mut witness, &[*byte]);
            }
        }
    }

    let ret = Witness {
        // Note: assumes little endian
        randomness: eth_types::U256::from_little_endian(&block.randomness.to_repr()),
        input: eth_types::Bytes::from(witness),
    };
    Ok(ret)
}

/// Gathers debug trace(s) from `rpc_url` for block `block_num` with `params`
/// created via the `gen_params` tool.
/// Expects a go-ethereum node with debug & archive capabilities on `rpc_url`.
pub async fn compute_proof(
    params: &Params<G1Affine>,
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
        let vk = keygen_vk(params, &circuit)?;
        let pk = keygen_pk(params, vk, &circuit)?;

        // Create randomness
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(params, &pk, &[circuit], &[], rng, &mut transcript)?;
        evm_proof = transcript.finalize();
    }

    {
        // generate state_circuit proof
        const N_ROWS: usize = 1 << 16;
        let circuit = StateCircuit::<Fr, N_ROWS>::new(block.randomness, block.rws);

        // TODO: same quest like in the first scope
        let vk = keygen_vk(params, &circuit)?;
        let pk = keygen_pk(params, vk, &circuit)?;

        // Create randomness
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(params, &pk, &[circuit], &[], rng, &mut transcript)?;
        state_proof = transcript.finalize();
    }

    let ret = Proofs {
        evm_proof: evm_proof.into(),
        state_proof: state_proof.into(),
    };

    Ok(ret)
}
