use super::{AccountMatch, StateTest, StateTestResult};
use crate::config::TestSuite;
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, FixedCParams},
    mock::BlockData,
};
use eth_types::{geth_types, Address, Bytes, Error, GethExecTrace, U256, U64};
use ethers_core::{
    k256::ecdsa::SigningKey,
    types::{transaction::eip2718::TypedTransaction, TransactionRequest},
};
use ethers_signers::{LocalWallet, Signer};
use external_tracer::TraceConfig;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use std::{collections::HashMap, str::FromStr};
use thiserror::Error;
use zkevm_circuits::{super_circuit::SuperCircuit, test_util::CircuitTestBuilder, witness::Block};

#[derive(PartialEq, Eq, Error, Debug)]
pub enum StateTestError {
    #[error("CannotGenerateCircuitInput({0})")]
    CircuitInput(String),
    #[error("BalanceMismatch(expected:{expected:?}, found:{found:?})")]
    BalanceMismatch { expected: U256, found: U256 },
    #[error("NonceMismatch(expected:{expected:?}, found:{found:?})")]
    NonceMismatch { expected: u64, found: u64 },
    #[error("CodeMismatch(expected: {expected:?}, found:{found:?})")]
    CodeMismatch { expected: Bytes, found: Bytes },
    #[error("StorgeMismatch(slot:{slot:?} expected:{expected:?}, found: {found:?})")]
    StorageMismatch {
        slot: U256,
        expected: U256,
        found: U256,
    },
    #[error("CircuitUnsatisfied(num_failure: {num_failure:?}  first: {first_failure:?}")]
    CircuitUnsatisfied {
        num_failure: usize,
        first_failure: String,
    },
    #[error("SkipTestMaxGasLimit({0})")]
    SkipTestMaxGasLimit(u64),
    #[error("SkipTestMaxSteps({0})")]
    SkipTestMaxSteps(usize),
    #[error("SkipTestSelfDestruct")]
    SkipTestSelfDestruct,
    #[error("SkipTestDifficulty")]
    SkipTestDifficulty,
    #[error("SkipTestBalanceOverflow")]
    SkipTestBalanceOverflow,
    #[error("Exception(expected:{expected:?}, found:{found:?})")]
    Exception { expected: bool, found: String },
}

impl StateTestError {
    pub fn is_skip(&self) -> bool {
        // Avoid lint `variant is never constructed`
        // We plan to add runtime-feature set in the future to include these skipping options
        let _ = StateTestError::SkipTestDifficulty;
        let _ = StateTestError::SkipTestBalanceOverflow;

        matches!(
            self,
            StateTestError::SkipTestMaxSteps(_)
                | StateTestError::SkipTestMaxGasLimit(_)
                | StateTestError::SkipTestSelfDestruct
        )
    }
}

#[derive(Default, Debug, Clone)]
pub struct CircuitsConfig {
    pub verbose: bool,
    pub super_circuit: bool,
}

fn check_post(
    builder: &CircuitInputBuilder<FixedCParams>,
    post: &HashMap<Address, AccountMatch>,
) -> Result<(), StateTestError> {
    log::trace!("check post");
    // check if the generated account data is the expected one
    for (address, expected) in post {
        let (_, actual) = builder.sdb.get_account(address);

        if expected.balance.map(|v| v == actual.balance) == Some(false) {
            log::error!("balance mismatch, expected {expected:?} actual {actual:?}");
            return Err(StateTestError::BalanceMismatch {
                expected: expected.balance.unwrap(),
                found: actual.balance,
            });
        }

        if expected.nonce.map(|v| v == actual.nonce) == Some(false) {
            log::error!("nonce mismatch, expected {expected:?} actual {actual:?}");
            return Err(StateTestError::NonceMismatch {
                expected: expected.nonce.unwrap(),
                found: actual.nonce,
            });
        }

        if let Some(expected_code) = &expected.code {
            let actual_code = (!actual.code_hash.is_zero())
                .then(|| {
                    builder
                        .code_db
                        .get_from_h256(&actual.code_hash)
                        .map(|bytecode| bytecode.code())
                        .expect("code exists")
                })
                .unwrap_or_default();
            if actual_code != expected_code.0 {
                return Err(StateTestError::CodeMismatch {
                    expected: expected_code.clone(),
                    found: Bytes::from(actual_code),
                });
            }
        }
        for (slot, expected_value) in &expected.storage {
            let actual_value = actual.storage.get(slot).cloned().unwrap_or_else(U256::zero);
            if expected_value != &actual_value {
                log::error!(
                    "StorageMismatch address {address:?}, expected {expected:?} actual {actual:?}"
                );
                return Err(StateTestError::StorageMismatch {
                    slot: *slot,
                    expected: *expected_value,
                    found: actual_value,
                });
            }
        }
    }
    log::trace!("check post done");
    Ok(())
}

fn into_traceconfig(st: StateTest) -> (String, TraceConfig, StateTestResult) {
    let chain_id = 1;
    let wallet = LocalWallet::from_str(&hex::encode(st.secret_key.0)).unwrap();
    let mut tx = TransactionRequest::new()
        .chain_id(chain_id)
        .from(st.from)
        .nonce(st.nonce)
        .value(st.value)
        .data(st.data.clone())
        .gas(st.gas_limit)
        .gas_price(st.gas_price);

    if let Some(to) = st.to {
        tx = tx.to(to);
    }
    let tx: TypedTransaction = tx.into();

    let sig = wallet.sign_transaction_sync(&tx).unwrap();

    (
        st.id,
        TraceConfig {
            chain_id: U256::one(),
            history_hashes: vec![U256::from_big_endian(st.env.previous_hash.as_bytes())],
            block_constants: geth_types::BlockConstants {
                coinbase: st.env.current_coinbase,
                timestamp: U256::from(st.env.current_timestamp),
                number: U64::from(st.env.current_number),
                difficulty: st.env.current_difficulty,
                gas_limit: U256::from(st.env.current_gas_limit),
                base_fee: st.env.current_base_fee,
            },

            transactions: vec![geth_types::Transaction {
                from: st.from,
                to: st.to,
                nonce: U64::from(st.nonce),
                value: st.value,
                gas_limit: U64::from(st.gas_limit),
                gas_price: st.gas_price,
                gas_fee_cap: U256::zero(),
                gas_tip_cap: U256::zero(),
                call_data: st.data,
                access_list: None,
                v: sig.v,
                r: sig.r,
                s: sig.s,
            }],
            accounts: st.pre.into_iter().collect(),
            ..Default::default()
        },
        st.result,
    )
}

pub fn geth_trace(st: StateTest) -> Result<GethExecTrace, StateTestError> {
    let (_, trace_config, _) = into_traceconfig(st);

    let mut geth_traces = external_tracer::trace(&trace_config)
        .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

    Ok(geth_traces.remove(0))
}

fn check_geth_traces(
    geth_traces: &[GethExecTrace],
    suite: &TestSuite,
    verbose: bool,
) -> Result<(), StateTestError> {
    if geth_traces.iter().any(|gt| {
        gt.struct_logs.iter().any(|sl| {
            sl.op == eth_types::evm_types::OpcodeId::SELFDESTRUCT
                || sl.op == eth_types::evm_types::OpcodeId::INVALID(0xff)
        })
    }) {
        return Err(StateTestError::SkipTestSelfDestruct);
    }

    if geth_traces[0].struct_logs.len() as u64 > suite.max_steps {
        return Err(StateTestError::SkipTestMaxSteps(
            geth_traces[0].struct_logs.len(),
        ));
    }

    if suite.max_gas > 0 && geth_traces[0].gas > suite.max_gas {
        return Err(StateTestError::SkipTestMaxGasLimit(geth_traces[0].gas));
    }
    if verbose {
        if let Err(e) = crate::utils::print_trace(geth_traces[0].clone()) {
            log::error!("fail to pretty print trace {e:?}");
        }
    }
    Ok(())
}

pub fn run_test(
    st: StateTest,
    suite: TestSuite,
    circuits_config: CircuitsConfig,
) -> Result<(), StateTestError> {
    // get the geth traces

    let (_, trace_config, post) = into_traceconfig(st.clone());

    let geth_traces = external_tracer::trace(&trace_config);

    let geth_traces = match (geth_traces, st.exception) {
        (Ok(res), false) => res,
        (Ok(_), true) => {
            return Err(StateTestError::Exception {
                expected: true,
                found: "no error".into(),
            })
        }
        (Err(_), true) => return Ok(()),
        (Err(err), false) => {
            if let Error::TracingError(ref err) = err {
                if err.contains("max initcode size exceeded") {
                    return Err(StateTestError::Exception {
                        expected: true,
                        found: err.to_string(),
                    });
                }
            }
            return Err(StateTestError::Exception {
                expected: false,
                found: err.to_string(),
            });
        }
    };

    check_geth_traces(&geth_traces, &suite, circuits_config.verbose)?;

    let transactions = trace_config
        .transactions
        .into_iter()
        .enumerate()
        .map(|(index, tx)| {
            tx.to_response(
                U64::from(index),
                trace_config.chain_id,
                trace_config.block_constants.number,
            )
        })
        .collect();

    let eth_block = eth_types::Block {
        author: Some(trace_config.block_constants.coinbase),
        timestamp: trace_config.block_constants.timestamp,
        number: Some(U64::from(trace_config.block_constants.number.as_u64())),
        difficulty: trace_config.block_constants.difficulty,
        gas_limit: trace_config.block_constants.gas_limit,
        base_fee_per_gas: Some(trace_config.block_constants.base_fee),
        transactions,
        ..eth_types::Block::default()
    };

    let wallet: LocalWallet = SigningKey::from_slice(&st.secret_key).unwrap().into();
    let mut wallets = HashMap::new();
    wallets.insert(
        wallet.address(),
        wallet.with_chain_id(trace_config.chain_id.as_u64()),
    );

    // process the transaction
    let mut geth_data = eth_types::geth_types::GethData {
        chain_id: trace_config.chain_id,
        history_hashes: trace_config.history_hashes.clone(),
        geth_traces: geth_traces.clone(),
        accounts: trace_config.accounts.values().cloned().collect(),
        eth_block: eth_block.clone(),
    };

    let mut builder;

    if !circuits_config.super_circuit {
        let circuits_params = FixedCParams {
            max_txs: 1,
            max_rws: 55000,
            max_calldata: 5000,
            max_bytecode: 5000,
            max_copy_rows: 55000,
            max_evm_rows: 0,
            max_exp_steps: 5000,
            max_keccak_rows: 0,
        };
        let block_data = BlockData::new_from_geth_data_with_params(geth_data, circuits_params);

        builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&eth_block, &geth_traces)
            .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

        let block: Block<Fr> =
            zkevm_circuits::evm_circuit::witness::block_convert(&builder).unwrap();

        CircuitTestBuilder::<1, 1>::new_from_block(block).run();
    } else {
        geth_data.sign(&wallets);

        let circuits_params = FixedCParams {
            max_txs: 1,
            max_calldata: 32,
            max_rws: 256,
            max_copy_rows: 256,
            max_exp_steps: 256,
            max_bytecode: 512,
            max_evm_rows: 0,
            max_keccak_rows: 0,
        };
        let (k, circuit, instance, _builder) =
            SuperCircuit::<Fr>::build(geth_data, circuits_params, Fr::from(0x100)).unwrap();
        builder = _builder;

        let prover = MockProver::run(k, &circuit, instance).unwrap();
        prover
            .verify_par()
            .map_err(|err| StateTestError::CircuitUnsatisfied {
                num_failure: err.len(),
                first_failure: err[0].to_string(),
            })?;
    };
    check_post(&builder, &post)?;

    Ok(())
}
