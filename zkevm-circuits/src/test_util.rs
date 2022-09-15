use crate::{state_circuit::StateCircuit, witness::Block};
use bus_mapping::mock::BlockData;
use eth_types::geth_types::{GethData, Transaction};
use ethers_core::types::{NameOrAddress, TransactionRequest};
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::dev::{MockProver, VerifyFailure};
use halo2_proofs::halo2curves::bn256::Fr;
use mock::TestContext;
use rand::{CryptoRng, Rng};

#[cfg(test)]
#[ctor::ctor]
fn init_env_logger() {
    // Enable RUST_LOG during tests
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("error")).init();
}

#[derive(Debug, Clone)]
pub struct BytecodeTestConfig {
    pub enable_evm_circuit_test: bool,
    pub enable_state_circuit_test: bool,
    pub gas_limit: u64,
}

impl Default for BytecodeTestConfig {
    fn default() -> Self {
        Self {
            enable_evm_circuit_test: true,
            enable_state_circuit_test: true,
            gas_limit: 1_000_000u64,
        }
    }
}

pub fn run_test_circuits<const NACC: usize, const NTX: usize>(
    test_ctx: TestContext<NACC, NTX>,
    config: Option<BytecodeTestConfig>,
) -> Result<(), Vec<VerifyFailure>> {
    let block: GethData = test_ctx.into();
    let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();

    // build a witness block from trace result
    let block = crate::witness::block_convert(&builder.block, &builder.code_db);

    // finish required tests according to config using this witness block
    test_circuits_using_witness_block(block, config.unwrap_or_default())
}

pub fn test_circuits_using_witness_block(
    block: Block<Fr>,
    config: BytecodeTestConfig,
) -> Result<(), Vec<VerifyFailure>> {
    // run evm circuit test
    if config.enable_evm_circuit_test {
        crate::evm_circuit::test::run_test_circuit(block.clone())?;
    }

    // run state circuit test
    // TODO: use randomness as one of the circuit public input, since randomness in
    // state circuit and evm circuit must be same
    if config.enable_state_circuit_test {
        const N_ROWS: usize = 1 << 16;
        let state_circuit = StateCircuit::<Fr>::new(block.randomness, block.rws, N_ROWS);
        let power_of_randomness = state_circuit.instance();
        let prover = MockProver::<Fr>::run(18, &state_circuit, power_of_randomness).unwrap();
        prover.verify_at_rows(
            N_ROWS - state_circuit.rows.len()..N_ROWS,
            N_ROWS - state_circuit.rows.len()..N_ROWS,
        )?
    }

    Ok(())
}

pub fn rand_tx<R: Rng + CryptoRng>(mut rng: R, chain_id: u64) -> Transaction {
    let wallet0 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
    let wallet1 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
    let from = wallet0.address();
    let to = wallet1.address();
    let data = b"hello";
    let tx = TransactionRequest::new()
        .chain_id(chain_id)
        .from(from)
        .to(to)
        .nonce(3)
        .value(1000)
        .data(data)
        .gas(500_000)
        .gas_price(1234);
    let sig = wallet0.sign_transaction_sync(&tx.clone().into());
    let to = tx.to.map(|to| match to {
        NameOrAddress::Address(a) => a,
        _ => unreachable!(),
    });
    Transaction {
        from: tx.from.unwrap(),
        to,
        gas_limit: tx.gas.unwrap(),
        gas_price: tx.gas_price.unwrap(),
        value: tx.value.unwrap(),
        call_data: tx.data.unwrap(),
        nonce: tx.nonce.unwrap(),
        v: sig.v,
        r: sig.r,
        s: sig.s,
        ..Transaction::default()
    }
}
