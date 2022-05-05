use anyhow::Context;
use bus_mapping::circuit_input_builder::CircuitInputBuilder;
use bus_mapping::mock::BlockData;
use eth_types::{
    evm_types::{Gas, OpcodeId},
    geth_types,
    geth_types::Account,
    Address, Bytes, GethExecTrace, H256, U256, U64,
};
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
    #[error("test skipped due {0} > max gas")]
    SkipTestMaxGasLimit(u64),
    #[error("test skipped unimplemented opcode {0}")]
    SkipUnimplementedOpcode(String),
}

pub struct StateTestConfig {
    pub max_gas: Gas,
    pub unimplemented_opcodes: Vec<OpcodeId>,
    pub run_circuit: bool,
}
impl Default for StateTestConfig {
    fn default() -> Self {
        Self {
            max_gas: Gas(1000000),
            unimplemented_opcodes: Vec::new(),
            run_circuit: true,
        }
    }
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
pub struct AccountMatch {
    pub address: Address,
    pub balance: Option<U256>,
    pub code: Option<Bytes>,
    pub nonce: Option<U256>,
    pub storage: HashMap<U256, U256>,
}

impl TryInto<Account> for AccountMatch {
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

type StateTestResult = HashMap<Address, AccountMatch>;

#[derive(PartialEq, Clone, Eq, Debug)]
pub struct StateTest {
    pub path: String,
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

impl std::fmt::Display for StateTest {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use prettytable::Table;
        let mut table = Table::new();
        table.add_row(row!["id", self.id]);
        table.add_row(row!["path", self.path]);
        table.add_row(row!["coinbase", format!("{:?}", self.env.current_coinbase)]);

        table.add_row(row![
            "difficulty",
            format!("{}", self.env.current_difficulty)
        ]);
        table.add_row(row!["number", format!("{}", self.env.current_number)]);
        table.add_row(row!["timestamp", format!("{}", self.env.current_timestamp)]);
        table.add_row(row!["prev_hash", format!("{:?}", self.env.previous_hash)]);
        table.add_row(row!["sk", format!("{}", hex::encode(&self.secret_key))]);
        table.add_row(row!["from", format!("{:?}", self.from)]);
        table.add_row(row!["to", format!("{:?}", self.to)]);
        table.add_row(row!["gas_limit", format!("{}", self.gas_limit)]);
        table.add_row(row!["gas_price", format!("{}", self.gas_price)]);
        table.add_row(row!["nonce", format!("{}", self.nonce)]);
        table.add_row(row!["value", format!("{}", self.value)]);
        table.add_row(row!["data", format!("{}", hex::encode(&self.data))]);

        let mut addrs: Vec<_> = self.pre.keys().collect();
        addrs.extend(self.result.keys());
        addrs.sort();
        addrs.dedup();
        for addr in addrs {
            let mut state = HashMap::new();
            if let Some(pre) = self.pre.get(addr) {
                state.insert("balance".to_string(), format!("{}", pre.balance));
                state.insert("nonce".to_string(), format!("{}", pre.nonce));
                state.insert("code".to_string(), format!("{}", hex::encode(&pre.code)));
                for (key, value) in &pre.storage {
                    let (k, v) = (format!("slot {}", key), format!("{}", value));
                    state.insert(k, v);
                }
            }
            if let Some(result) = self.result.get(addr) {
                let none = String::from("∅");
                if let Some(balance) = result.balance {
                    let pre = state.get("balance").unwrap_or(&none);
                    let text = format!("{} → {}", pre, balance);
                    state.insert("balance".to_string(), text);
                }
                if let Some(code) = &result.code {
                    let pre = state.get("code").unwrap_or(&none);
                    let text = format!("{} → {}", pre, code);
                    state.insert("code".to_string(), text);
                }
                if let Some(nonce) = &result.nonce {
                    let pre = state.get("nonce").unwrap_or(&none);
                    let text = format!("{} → {}", pre, nonce);
                    state.insert("nonce".to_string(), text);
                }
                for (key, value) in &result.storage {
                    let (k, v) = (format!("slot {}", key), format!("{}", value));
                    let pre = state.get(&k).unwrap_or(&none);
                    let text = format!("{} → {}", pre, v);
                    state.insert(k, text);
                }
            }
            let mut text = String::new();
            let max_len = 100;
            let mut keys: Vec<_> = state.keys().collect();
            keys.sort();
            for k in keys {
                let v = state.get(k).unwrap();
                let max_len = max_len - k.len();
                for i in 0..=v.len() / max_len {
                    if i == 0 {
                        text.push_str(&k);
                        text.push_str(": ");
                    } else {
                        let padding: String = std::iter::repeat(" ").take(k.len() + 2).collect();
                        text.push_str(&padding);
                    }
                    text.push_str(&v[i * max_len..std::cmp::min((i + 1) * max_len, v.len())]);
                    text.push_str("\n");
                }
            }
            table.add_row(row![format!("{:?}", addr), text]);
        }
        write!(f, "{}", table.to_string())?;

        Ok(())
    }
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
    pub fn check_post(
        builder: &CircuitInputBuilder,
        post: &HashMap<Address, AccountMatch>,
    ) -> Result<(), StateTestError> {
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

            if let Some(expected_code) = &expected.code {
                let actual_code = if actual.code_hash.is_zero() {
                    std::borrow::Cow::Owned(Vec::new())
                } else {
                    std::borrow::Cow::Borrowed(&builder.code_db.0[&actual.code_hash])
                };
                if &actual_code as &[u8] != expected_code.0 {
                    return Err(StateTestError::CodeMismatch {
                        expected: expected_code.clone(),
                        found: Bytes::from(actual_code.to_vec()),
                    });
                }
            }
            for (slot, expected_value) in &expected.storage {
                let actual_value = actual.storage.get(&slot).cloned().unwrap_or(U256::zero());
                if expected_value != &actual_value {
                    return Err(StateTestError::StorageMismatch {
                        slot: slot.clone(),
                        expected: expected_value.clone(),
                        found: actual_value,
                    });
                }
            }
        }
        Ok(())
    }

    pub fn test_circuit(self, builder: &CircuitInputBuilder) {
        // build a witness block from trace result
        let block =
            zkevm_circuits::evm_circuit::witness::block_convert(&builder.block, &builder.code_db);

        // finish requiered tests according to config using this witness block
        zkevm_circuits::evm_circuit::test::run_test_circuit_incomplete_fixed_table(block)
            .expect("circuit should pass");
    }

    pub fn geth_trace(self) -> Result<GethExecTrace, StateTestError> {
        let (_, trace_config, _) = self.clone().into_traceconfig();

        let mut geth_traces = external_tracer::trace(&trace_config)
            .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

        Ok(geth_traces.remove(0))
    }

    pub fn run(self, config: &StateTestConfig) -> Result<(), StateTestError> {
        // get the geth traces
        let (_, trace_config, post) = self.clone().into_traceconfig();

        let geth_traces = external_tracer::trace(&trace_config)
            .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

        // we are not checking here geth_traces[0].failed, since
        // there are some tests that makes the tx failing
        // (eg memory filler tests)

        if let Some(step) = geth_traces[0]
            .struct_logs
            .iter()
            .find(|step| config.unimplemented_opcodes.contains(&step.op))
        {
            return Err(StateTestError::SkipUnimplementedOpcode(format!(
                "{:?}",
                step.op
            )));
        }

        if geth_traces[0].gas > config.max_gas {
            return Err(StateTestError::SkipTestMaxGasLimit(geth_traces[0].gas.0));
        }

        let builder = Self::create_input_builder(trace_config, geth_traces)?;

        Self::check_post(&builder, &post)?;

        if config.run_circuit {
            Self::test_circuit(self, &builder);
        }
        Ok(())
    }

    fn create_input_builder(
        trace_config: TraceConfig,
        geth_traces: Vec<GethExecTrace>,
    ) -> Result<CircuitInputBuilder, StateTestError> {
        let transactions = trace_config
            .transactions
            .into_iter()
            .enumerate()
            .map(|(index, tx)| eth_types::Transaction {
                from: tx.from,
                to: tx.to,
                value: tx.value,
                input: tx.call_data,
                gas_price: Some(tx.gas_price),
                access_list: tx.access_list,
                nonce: tx.nonce,
                gas: tx.gas_limit,
                transaction_index: Some(U64::from(index)),
                ..eth_types::Transaction::default()
            })
            .collect();

        let eth_block = eth_types::Block {
            author: trace_config.block_constants.coinbase,
            timestamp: trace_config.block_constants.timestamp,
            number: Some(U64::from(trace_config.block_constants.timestamp.as_u64())),
            difficulty: trace_config.block_constants.difficulty,
            gas_limit: trace_config.block_constants.gas_limit,
            base_fee_per_gas: Some(trace_config.block_constants.base_fee),
            transactions,
            ..eth_types::Block::default()
        };

        // process the transaction
        let geth_data = eth_types::geth_types::GethData {
            chain_id: trace_config.chain_id,
            history_hashes: trace_config.history_hashes.clone(),
            geth_traces: geth_traces.clone(),
            accounts: trace_config.accounts.values().cloned().collect(),
            eth_block: eth_block.clone(),
        };

        let block_data = BlockData::new_from_geth_data(geth_data);
        let mut builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&eth_block, &geth_traces)
            .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

        Ok(builder)
    }
}
