use anyhow::Context;
use eth_types::{geth_types, geth_types::Account, Address, Bytes, H256, U256, U64};
use external_tracer::TraceConfig;
use std::collections::HashMap;
use thiserror::Error;

#[derive(PartialEq, Eq, Error, Debug)]
pub enum StateTestError {
    #[error("cannot generate circuit input: `{0}`")]
    CircuitInput(String),
    #[error("balance mismatch (expected {expected:?}, found {found:?})")]
    BalanceMismatch { expected: U256, found: U256 },
    #[error("nonce mismatch (expected {expected:?}, found {found:?})")]
    NonceMismatch { expected: U256, found: U256 },
    #[error("code mismatch (expected {expected:?}, found {found:?})")]
    CodeMismatch { expected: Bytes, found: Bytes },
    #[error("storage mismatch slot={slot:?} (expected {expected:?}, found {found:?})")]
    StorageMismatch {
        slot: U256,
        expected: U256,
        found: U256,
    },
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Env {
    pub current_coinbase: Address,
    pub current_difficulty: U256,
    pub current_gas_limit: u64,
    pub current_number: u64,
    pub current_timestamp: u64,
    pub previous_hash: H256,
}

#[derive(PartialEq, Eq, Default, Debug, Clone)]
pub struct PartialAccount {
    pub address: Address,
    pub balance: Option<U256>,
    pub code: Option<Bytes>,
    pub nonce: Option<U256>,
    pub storage: HashMap<U256, U256>,
}

impl TryInto<Account> for PartialAccount {
    type Error = anyhow::Error;
    fn try_into(self) -> Result<Account, Self::Error> {
        Ok(Account {
            address: self.address,
            balance: self.balance.context("balance")?,
            code: self.code.context("code")?,
            nonce: self.nonce.context("nonce")?,
            storage: self.storage,
        })
    }
}

type StateTestResult = HashMap<Address, PartialAccount>;

#[derive(PartialEq, Eq, Debug)]
pub struct StateTest {
    pub id: String,
    pub env: Env,
    pub secret_key: Bytes,
    pub from: Address,
    pub to: Option<Address>,
    pub gas_limit: u64,
    pub gas_price: U256,
    pub nonce: U256,
    pub value: U256,
    pub data: Bytes,
    pub pre: HashMap<Address, Account>,
    pub result: StateTestResult,
}

impl StateTest {
    fn into_traceconfig(self) -> (String, TraceConfig, StateTestResult) {
        (
            self.id,
            TraceConfig {
                chain_id: U256::one(),
                history_hashes: Vec::new(),
                block_constants: geth_types::BlockConstants {
                    coinbase: self.env.current_coinbase,
                    timestamp: U256::from(self.env.current_timestamp),
                    number: U64::from(self.env.current_number),
                    difficulty: self.env.current_difficulty,
                    gas_limit: U256::from(self.env.current_gas_limit),
                    base_fee: U256::one(),
                },
                transactions: vec![geth_types::Transaction {
                    from: self.from,
                    to: self.to,
                    nonce: self.nonce,
                    value: self.value,
                    gas_limit: U256::from(self.gas_limit),
                    gas_price: self.gas_price,
                    gas_fee_cap: U256::zero(),
                    gas_tip_cap: U256::zero(),
                    call_data: self.data,
                    access_list: None,
                }],
                accounts: self.pre,
            },
            self.result,
        )
    }
    pub fn run(self, test_circuit: bool) -> Result<(), StateTestError> {
        // get the geth traces
        let (_, trace_config, post) = self.into_traceconfig();
        let builder = crate::exec::traceconfig(trace_config)
            .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

        // check if the generated account data is the expected one
        for (address, expected) in post {
            let (_, actual) = builder.sdb.get_account(&address);

            if expected.balance.map(|v| v == actual.balance) == Some(false) {
                return Err(StateTestError::BalanceMismatch {
                    expected: expected.balance.unwrap(),
                    found: actual.balance,
                });
            }

            if expected.nonce.map(|v| v == actual.nonce) == Some(false) {
                return Err(StateTestError::NonceMismatch {
                    expected: expected.nonce.unwrap(),
                    found: actual.nonce,
                });
            }

            if let Some(expected_code) = expected.code {
                let actual_code = if actual.code_hash.is_zero() {
                    std::borrow::Cow::Owned(Vec::new())
                } else {
                    std::borrow::Cow::Borrowed(&builder.code_db.0[&actual.code_hash])
                };
                if &actual_code as &[u8] != expected_code.0 {
                    return Err(StateTestError::CodeMismatch {
                        expected: expected_code,
                        found: Bytes::from(actual_code.to_vec()),
                    });
                }
            }
            for (slot, expected_value) in expected.storage {
                let actual_value = actual.storage.get(&slot).cloned().unwrap_or(U256::zero());
                if expected_value != actual_value {
                    return Err(StateTestError::StorageMismatch {
                        slot,
                        expected: expected_value,
                        found: actual_value,
                    });
                }
            }
        }
        Ok(())
    }
}
