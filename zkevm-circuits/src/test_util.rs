//! Testing utilities



use crate::{
    evm_circuit::{
        test::{get_test_cicuit_from_block, get_test_degree},
        EvmCircuit,
    },
    state_circuit::StateCircuit,
    util::SubCircuit,
    witness::{Block, Rw},
};
use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
use eth_types::geth_types::{GethData, Transaction};
use ethers_core::{
    types::{NameOrAddress, TransactionRequest},
};
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::dev::{MockProver};
use halo2_proofs::halo2curves::bn256::Fr;
use mock::TestContext;
use rand::{CryptoRng, Rng};

#[cfg(test)]
#[ctor::ctor]
fn init_env_logger() {
    // Enable RUST_LOG during tests
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("error")).init();
}

/// Bytecode circuit test configuration
#[derive(Debug, Clone)]
pub struct BytecodeTestConfig {
    /// Test EVM circuit
    pub enable_evm_circuit_test: bool,
    /// Test state circuit
    pub enable_state_circuit_test: bool,
    /// Gas limit
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

pub(crate) struct CircuitTestBuilder<const NACC: usize, const NTX: usize> {
    test_ctx: Option<TestContext<NACC, NTX>>,
    bytecode_config: Option<BytecodeTestConfig>,
    circuit_params: Option<CircuitsParams>,
    block: Option<Block<Fr>>,
    evm_checks: Option<Box<dyn Fn(MockProver<Fr>)>>,
    state_checks: Option<Box<dyn Fn(MockProver<Fr>)>>,
    block_modifiers: Vec<Box<dyn Fn(&mut Block<Fr>)>>,
}

impl<const NACC: usize, const NTX: usize> CircuitTestBuilder<NACC, NTX> {
    pub fn empty() -> Self {
        CircuitTestBuilder {
            test_ctx: None,
            bytecode_config: None,
            circuit_params: None,
            block: None,
            evm_checks: Some(Box::new(|prover| prover.assert_satisfied_par())),
            state_checks: Some(Box::new(|prover| prover.assert_satisfied_par())),
            block_modifiers: vec![],
        }
    }

    pub fn test_ctx(mut self, ctx: TestContext<NACC, NTX>) -> Self {
        self.test_ctx = Some(ctx);
        self
    }

    pub fn config(mut self, config: BytecodeTestConfig) -> Self {
        self.bytecode_config = Some(config);
        self
    }

    pub fn params(mut self, params: CircuitsParams) -> Self {
        self.circuit_params = Some(params);
        self
    }

    pub fn block(mut self, block: Block<Fr>) -> Self {
        self.block = Some(block);
        self
    }

    pub fn state_checks(mut self, state_checks: Box<dyn Fn(MockProver<Fr>)>) -> Self {
        self.state_checks = Some(state_checks);
        self
    }

    pub fn evm_checks(mut self, evm_checks: Box<dyn Fn(MockProver<Fr>)>) -> Self {
        self.evm_checks = Some(evm_checks);
        self
    }

    pub fn block_modifier(mut self, modifier: Box<dyn Fn(&mut Block<Fr>)>) -> Self {
        self.block_modifiers.push(modifier);
        self
    }
}

impl<const NACC: usize, const NTX: usize> CircuitTestBuilder<NACC, NTX> {
    pub fn run(self) {
        let block: Block<Fr> = if self.block.is_some() {
            self.block.unwrap()
        } else if self.test_ctx.is_some() {
            let block: GethData = self.test_ctx.unwrap().into();
            let mut builder = BlockData::new_from_geth_data_with_params(
                block.clone(),
                self.circuit_params.unwrap_or_default(),
            )
            .new_circuit_input_builder();
            builder
                .handle_block(&block.eth_block, &block.geth_traces)
                .unwrap();
            // Build a witness block from trace result.
            let mut block =
                crate::witness::block_convert(&builder.block, &builder.code_db).unwrap();

            for modifier_fn in self.block_modifiers {
                modifier_fn.as_ref()(&mut block);
            }
            block
        } else {
            panic!("No attribute to build a block was passed to the CircuitTestBuilder")
        };

        // Fetch Bytecode TestConfig
        let config = self.bytecode_config.unwrap_or_default();

        // Run evm circuit test
        if config.enable_evm_circuit_test {
            let k = get_test_degree(&block);

            let (_active_gate_rows, _active_lookup_rows) = EvmCircuit::<Fr>::get_active_rows(&block);

            let circuit = get_test_cicuit_from_block(block.clone());
            let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();

            //prover.verify_at_rows_par(active_gate_rows.into_iter(),
            // active_lookup_rows.into_iter())
            self.evm_checks.unwrap().as_ref()(prover)
        }

        // Run state circuit test
        // TODO: use randomness as one of the circuit public input, since randomness in
        // state circuit and evm circuit must be same
        if config.enable_state_circuit_test {
            const N_ROWS: usize = 1 << 16;
            let state_circuit = StateCircuit::<Fr>::new(block.rws, N_ROWS);
            let power_of_randomness = state_circuit.instance();
            let prover = MockProver::<Fr>::run(18, &state_circuit, power_of_randomness).unwrap();
            // Skip verification of Start rows to accelerate testing
            let _non_start_rows_len = state_circuit
                .rows
                .iter()
                .filter(|rw| !matches!(rw, Rw::Start { .. }))
                .count();

            // prover
            //     .verify_at_rows(
            //         N_ROWS - non_start_rows_len..N_ROWS,
            //         N_ROWS - non_start_rows_len..N_ROWS,
            //     )
            //     .unwrap()
            self.state_checks.unwrap().as_ref()(prover);
        }
    }
}

/// generate rand tx for pi circuit -> TODO: Move to `mock`.
pub fn rand_tx<R: Rng + CryptoRng>(mut rng: R, chain_id: u64, has_calldata: bool) -> Transaction {
    let wallet0 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
    let wallet1 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
    let from = wallet0.address();
    let to = wallet1.address();
    let data = if has_calldata {
        let mut data = b"helloworld".to_vec();
        data[0] = 0;
        data[2] = 0;
        data
    } else {
        vec![]
    };
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
