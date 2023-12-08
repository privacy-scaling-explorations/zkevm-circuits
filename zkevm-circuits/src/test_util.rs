//! Testing utilities

use crate::{
    evm_circuit::{cached::EvmCircuitCached, EvmCircuit},
    state_circuit::StateCircuit,
    util::SubCircuit,
    witness::{Block, Chunk, Rw},
};
use bus_mapping::{
    circuit_input_builder::{FixedCParams},
    mock::BlockData,
};
use eth_types::geth_types::GethData;
use std::cmp;

use crate::util::log2_ceil;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use mock::TestContext;

#[cfg(test)]
#[ctor::ctor]
fn init_env_logger() {
    // Enable RUST_LOG during tests
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("error")).init();
}

const NUM_BLINDING_ROWS: usize = 64;

#[allow(clippy::type_complexity)]
/// Struct used to easily generate tests for EVM &| State circuits being able to
/// customize all of the steps involved in the testing itself.
///
/// By default, the tests run through `prover.assert_satisfied_par()` but the
/// builder pattern provides functions that allow to pass different functions
/// that the prover should execute when verifying the CTB correctness.
///
/// The CTB also includes a mechanism to recieve calls that will modify the
/// block produced from the [`TestContext`] and apply them before starting to
/// compute the proof.
///
/// ## Example:
/// ```rust, no_run
/// use eth_types::geth_types::Account;
/// use eth_types::{address, bytecode, Address, Bytecode, ToWord, Word, U256, word};
/// use mock::{TestContext, MOCK_ACCOUNTS, gwei, eth};
/// use zkevm_circuits::test_util::CircuitTestBuilder;
///     let code = bytecode! {
/// // [ADDRESS, STOP]
///     PUSH32(word!("
/// 3000000000000000000000000000000000000000000000000000000000000000"))
///     PUSH1(0)
///     MSTORE
///
///     PUSH1(2)
///     PUSH1(0)
///     RETURN
/// };
/// let ctx = TestContext::<1, 1>::new(
///     None,
///     |accs| {
///         accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
///     },
///     |mut txs, _accs| {
///         txs[0]
///             .from(MOCK_ACCOUNTS[0])
///             .gas_price(gwei(2))
///             .gas(Word::from(0x10000))
///             .value(eth(2))
///             .input(code.into());
///     },
///     |block, _tx| block.number(0xcafeu64),
/// )
/// .unwrap();
///
/// CircuitTestBuilder::new_from_test_ctx(ctx)
///     .modifier(Box::new(|block| chunk.fixed_param.max_evm_rows = (1 << 18) - 100))
///     .state_checks(Box::new(|prover, evm_rows, lookup_rows| assert!(prover.verify_at_rows_par(evm_rows.iter().cloned(), lookup_rows.iter().cloned()).is_err())))
///     .run();
/// ```
pub struct CircuitTestBuilder<const NACC: usize, const NTX: usize> {
    test_ctx: Option<TestContext<NACC, NTX>>,
    circuits_params: Option<FixedCParams>,
    block: Option<Block<Fr>>,
    chunk: Option<Chunk<Fr>>,
    evm_checks: Box<dyn Fn(MockProver<Fr>, &Vec<usize>, &Vec<usize>)>,
    state_checks: Box<dyn Fn(MockProver<Fr>, &Vec<usize>, &Vec<usize>)>,
    modifiers: Vec<Box<dyn Fn(&mut Block<Fr>, &mut Chunk<Fr>)>>,
}

impl<const NACC: usize, const NTX: usize> CircuitTestBuilder<NACC, NTX> {
    /// Generates an empty/set to default `CircuitTestBuilder`.
    fn empty() -> Self {
        CircuitTestBuilder {
            test_ctx: None,
            circuits_params: None,
            block: None,
            chunk: None,
            evm_checks: Box::new(|prover, gate_rows, lookup_rows| {
                prover.assert_satisfied_at_rows_par(
                    gate_rows.iter().cloned(),
                    lookup_rows.iter().cloned(),
                )
            }),
            state_checks: Box::new(|prover, gate_rows, lookup_rows| {
                prover.assert_satisfied_at_rows_par(
                    gate_rows.iter().cloned(),
                    lookup_rows.iter().cloned(),
                )
            }),
            modifiers: vec![],
        }
    }

    /// Generates a CTBC from a [`TestContext`] passed with all the other fields
    /// set to [`Default`].
    pub fn new_from_test_ctx(ctx: TestContext<NACC, NTX>) -> Self {
        Self::empty().test_ctx(ctx)
    }

    /// Generates a CTBC from a [`Block`] passed with all the other fields
    /// set to [`Default`].
    pub fn new_from_block(block: Block<Fr>) -> Self {
        Self::empty().block(block)
    }

    /// Allows to produce a [`TestContext`] which will serve as the generator of
    /// the Block.
    pub fn test_ctx(mut self, ctx: TestContext<NACC, NTX>) -> Self {
        self.test_ctx = Some(ctx);
        self
    }

    /// Allows to pass a non-default [`FixedCParams`] to the builder.
    /// This means that we can increase for example, the `max_rws` or `max_txs`.
    pub fn params(mut self, params: FixedCParams) -> Self {
        assert!(
            self.block.is_none(),
            "circuit_params already provided in the block"
        );
        self.circuits_params = Some(params);
        self
    }

    /// Allows to pass a [`Block`] already built to the constructor.
    pub fn block(mut self, block: Block<Fr>) -> Self {
        self.block = Some(block);
        self
    }

    #[allow(clippy::type_complexity)]
    /// Allows to provide checks different than the default ones for the State
    /// Circuit verification.
    pub fn state_checks(
        mut self,
        state_checks: Box<dyn Fn(MockProver<Fr>, &Vec<usize>, &Vec<usize>)>,
    ) -> Self {
        self.state_checks = state_checks;
        self
    }

    #[allow(clippy::type_complexity)]
    /// Allows to provide checks different than the default ones for the EVM
    /// Circuit verification.
    pub fn evm_checks(
        mut self,
        evm_checks: Box<dyn Fn(MockProver<Fr>, &Vec<usize>, &Vec<usize>)>,
    ) -> Self {
        self.evm_checks = evm_checks;
        self
    }

    #[allow(clippy::type_complexity)]
    /// Allows to provide modifier functions for the [`Block`] and [`Chunk`] that will be
    /// generated within this builder.
    ///
    /// That removes the need in a lot of tests to build the block outside of
    /// the builder because they need to modify something particular.
    pub fn modifier(mut self, modifier: Box<dyn Fn(&mut Block<Fr>, &mut Chunk<Fr>)>) -> Self {
        self.modifiers.push(modifier);
        self
    }
}

impl<const NACC: usize, const NTX: usize> CircuitTestBuilder<NACC, NTX> {
    /// Triggers the `CircuitTestBuilder` to convert the [`TestContext`] if any,
    /// into a [`Block`] and specified numbers of [`Chunk`]s
    /// and apply the default or provided modifiers or
    /// circuit checks to the provers generated for the State and EVM circuits.
    /// One [`Chunk`] is generated by default and the first one is run unless 
    /// [`FixedCParams`] is set.
    pub fn run(self) {
        if let Some(fixed_params) = self.circuits_params {
            self.run_dynamic_chunk(fixed_params.total_chunks, 0);
        } else {
            self.run_dynamic_chunk(1, 0);
        }
    }

    /// Triggers the `CircuitTestBuilder` to convert the [`TestContext`] if any,
    /// into a [`Block`] and specified numbers of [`Chunk`]s.
    /// [`FixedCParams`] must be set to build the amount of chunks 
    /// and run the indexed [`Chunk`].
    pub fn run_chunk(self, chunk_index: usize) {
        let total_chunk = self
            .circuits_params
            .expect("Fixed param not specified")
            .total_chunks;
        self.run_dynamic_chunk(total_chunk, chunk_index);
    }

    /// Triggers the `CircuitTestBuilder` to convert the [`TestContext`] if any,
    /// into a [`Block`] and specified numbers of [`Chunk`]s with dynamic chunk size
    /// if [`FixedCParams`] is not set, otherwise the `total_chunk` must matched.
    pub fn run_dynamic_chunk(self, total_chunk: usize, chunk_index: usize) {
        assert!(chunk_index < total_chunk, "Chunk index exceed total chunks");
        let (block, chunk) = if self.block.is_some() && self.chunk.is_some() {
            (self.block.unwrap(), self.chunk.unwrap())
        } else if self.test_ctx.is_some() {
            let block: GethData = self.test_ctx.unwrap().into();

            let builder = match self.circuits_params {
                Some(fixed_param) => {
                    assert_eq!(
                        fixed_param.total_chunks, total_chunk,
                        "Total chunks unmatched with fixed param"
                    );
                    BlockData::new_from_geth_data_with_params(block.clone(), fixed_param)
                        .new_circuit_input_builder()
                        .handle_block(&block.eth_block, &block.geth_traces)
                        .unwrap()
                }
                None => BlockData::new_from_geth_data_chunked(block.clone(), total_chunk)
                    .new_circuit_input_builder()
                    .handle_block(&block.eth_block, &block.geth_traces)
                    .unwrap(),
            };

            // FIXME(Cecilia): debug
            builder.chunks.iter().for_each(|c| {
                println!(
                    "{:?}\n{:?}\nbegin {:?}\nend {:?}\n",
                    c.ctx,
                    c.fixed_param,
                    c.begin_chunk.is_some(),
                    c.end_chunk.is_some()
                );
                println!("----------");
            });
            println!("block rwc = {:?}", builder.block_ctx.rwc);

            // Build a witness block from trace result.
            let mut block = crate::witness::block_convert(&builder).unwrap();
            let mut chunk = crate::witness::chunk_convert(&builder, chunk_index).unwrap();

            println!("fingerprints = {:?}", chunk.rw_fingerprint);

            for modifier_fn in self.modifiers {
                modifier_fn.as_ref()(&mut block, &mut chunk);
            }
            (block, chunk)
        } else {
            panic!("No attribute to build a block was passed to the CircuitTestBuilder")
        };
        let params = chunk.fixed_param;

        // Run evm circuit test
        {
            let k = block.get_test_degree(&chunk);

            let (_active_gate_rows, _active_lookup_rows) =
                EvmCircuit::<Fr>::get_active_rows(&block, &chunk);

            let circuit =
                EvmCircuitCached::get_test_circuit_from_block(block.clone(), chunk.clone());
            let instance = circuit.instance();
            let _prover = MockProver::<Fr>::run(k, &circuit, instance).unwrap();

            // self.evm_checks.as_ref()(prover, &active_gate_rows, &active_lookup_rows)
        }

        // Run state circuit test
        // TODO: use randomness as one of the circuit public input, since randomness in
        // state circuit and evm circuit must be same
        {
            let rows_needed = StateCircuit::<Fr>::min_num_rows_block(&block, &chunk).1;
            let k = cmp::max(log2_ceil(rows_needed + NUM_BLINDING_ROWS), 18);
            let state_circuit = StateCircuit::<Fr>::new(chunk.rws.clone(), params.max_rws, &chunk);
            let instance = state_circuit.instance();
            let _prover = MockProver::<Fr>::run(k, &state_circuit, instance).unwrap();
            // Skip verification of Start rows to accelerate testing
            let non_start_rows_len = state_circuit
                .rows
                .iter()
                .filter(|rw| !matches!(rw, Rw::Padding { .. }))
                .count();
            let _rows: Vec<usize> = (params.max_rws - non_start_rows_len..params.max_rws).collect();

            // self.state_checks.as_ref()(prover, &rows, &rows);
        }
    }
}
