#![allow(dead_code, unused_imports)]

use super::spec::{AccountMatch, Env, StateTest};
use crate::abi;
use crate::compiler::Compiler;
use crate::utils::MainnetFork;
use anyhow::{bail, Context, Result};
use eth_types::evm_types::OpcodeId;
use eth_types::{geth_types::Account, Address, Bytes, H256, U256};
use ethers_core::k256::ecdsa::SigningKey;
use ethers_core::utils::secret_key_to_address;
use serde::Deserialize;
use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::RangeBounds;
use std::str::FromStr;
use yaml_rust::Yaml;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TestEnv {
    current_coinbase: String,
    current_difficulty: String,
    current_gas_limit: String,
    current_number: String,
    current_timestamp: String,
    previous_hash: String,
}

#[derive(Debug, Clone, Deserialize)]
struct Indexes {
    data: serde_json::value::Value,
    gas: serde_json::value::Value,
    value: serde_json::value::Value,
}

#[derive(Debug, Clone, Deserialize)]
struct AccountPost {
    balance: Option<String>,
    code: Option<String>,
    nonce: Option<String>,
    storage: Option<HashMap<String, String>>,
    shouldnotexist: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
struct AccountPre {
    balance: String,
    code: String,
    nonce: String,
    storage: HashMap<String, String>,
}

#[derive(Debug, Clone, Deserialize)]
struct Expect {
    indexes: Indexes,
    network: Vec<String>,
    result: HashMap<String, AccountPost>,
}

#[derive(Debug, Clone, Deserialize)]
struct JsonStateTest {
    env: TestEnv,
    transaction: Transaction,
    pre: HashMap<String, AccountPre>,
    expect: Vec<Expect>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Transaction {
    data: Vec<String>,
    gas_limit: Vec<String>,
    gas_price: String,
    nonce: String,
    secret_key: String,
    to: String,
    value: Vec<String>,
}

#[derive(Debug, Clone)]
enum Ref {
    Any,
    Index(usize),
}

struct Refs(Vec<Ref>);

impl Refs {
    fn contains_index(&self, idx: usize) -> bool {
        self.0.iter().any(|r| match r {
            Ref::Index(i) => i == &idx,
            Ref::Any => true,
        })
    }
}

pub struct JsonStateTestBuilder<'a> {
    compiler: &'a mut Compiler,
}

impl<'a> JsonStateTestBuilder<'a> {
    pub fn new(compiler: &'a mut Compiler) -> Self {
        Self { compiler }
    }

    /// generates `StateTest` vectors from a ethereum josn test specification
    pub fn load_json(&mut self, path: &str, source: &str) -> Result<Vec<StateTest>> {
        let mut state_tests = Vec::new();
        let tests: HashMap<String, JsonStateTest> = serde_json::from_str(source)?;

        for (test_name, test) in tests {
            let env = Self::parse_env(&test.env)?;
            let pre = self.parse_accounts_pre(&test.pre)?;

            let to = Self::parse_to_address(&test.transaction.to)?;
            let secret_key = Self::parse_bytes(&test.transaction.secret_key)?;
            let from = secret_key_to_address(&SigningKey::from_bytes(&secret_key.to_vec())?);
            let nonce = Self::parse_u256(&test.transaction.nonce)?;
            let gas_price = Self::parse_u256(&test.transaction.gas_price)?;

            let data_s: Vec<_> = test
                .transaction
                .data
                .iter()
                .map(|item| self.parse_calldata(item))
                .collect::<Result<_>>()?;

            let gas_limit_s: Vec<_> = test
                .transaction
                .gas_limit
                .iter()
                .map(|item| Self::parse_u64(item))
                .collect::<Result<_>>()?;

            let value_s: Vec<_> = test
                .transaction
                .value
                .iter()
                .map(|item| Self::parse_u256(item))
                .collect::<Result<_>>()?;

            let mut expects = Vec::new();
            for expect in test.expect {
                let data_refs = Self::parse_refs(&expect.indexes.data)?;
                let gas_refs = Self::parse_refs(&expect.indexes.gas)?;
                let value_refs = Self::parse_refs(&expect.indexes.value)?;
                let result = self.parse_accounts_post(&expect.result)?;

                if MainnetFork::in_network_range(&expect.network)? {
                    expects.push((data_refs, gas_refs, value_refs, result));
                }
            }

            for (idx_data, data) in data_s.iter().enumerate() {
                for (idx_gas, gas_limit) in gas_limit_s.iter().enumerate() {
                    for (idx_value, value) in value_s.iter().enumerate() {
                        for (data_refs, gas_refs, value_refs, result) in &expects {
                            if !data_refs.contains_index(idx_data) {
                                continue;
                            }

                            if !gas_refs.contains_index(idx_gas) {
                                continue;
                            }

                            if !value_refs.contains_index(idx_value) {
                                continue;
                            }

                            state_tests.push(StateTest {
                                path: path.to_string(),
                                id: format!(
                                    "{}_d{}_g{}_v{}",
                                    test_name, idx_data, idx_gas, idx_value
                                ),
                                env: env.clone(),
                                pre: pre.clone(),
                                result: result.clone(),
                                from,
                                to,
                                secret_key: secret_key.clone(),
                                nonce,
                                gas_price,
                                gas_limit: *gas_limit,
                                value: *value,
                                data: eth_types::Bytes(data.0.clone()),
                                exception: false, // TODO: check
                            });
                        }
                    }
                }
            }
        }

        Ok(state_tests)
    }

    /// parse env section
    fn parse_env(env: &TestEnv) -> Result<Env> {
        Ok(Env {
            current_coinbase: Self::parse_address(&env.current_coinbase)?,
            current_difficulty: Self::parse_u256(&env.current_difficulty)?,
            current_gas_limit: Self::parse_u64(&env.current_gas_limit)?,
            current_number: Self::parse_u64(&env.current_number)?,
            current_timestamp: Self::parse_u64(&env.current_timestamp)?,
            previous_hash: Self::parse_hash(&env.previous_hash)?,
        })
    }

    /// parse a vector of address=>(storage,balance,code,nonce) entry
    fn parse_accounts_pre(
        &mut self,
        accounts_pre: &HashMap<String, AccountPre>,
    ) -> Result<HashMap<Address, Account>> {
        let mut accounts = HashMap::new();
        for (address, acc) in accounts_pre {
            let address = Self::parse_address(address)?;
            let mut storage = HashMap::new();
            for (k, v) in &acc.storage {
                storage.insert(Self::parse_u256(k)?, Self::parse_u256(v)?);
            }
            let account = Account {
                address,
                balance: Self::parse_u256(&acc.balance)?,
                nonce: Self::parse_u256(&acc.nonce)?,
                code: self.parse_code(&acc.code)?,
                storage,
            };
            accounts.insert(address, account);
        }
        Ok(accounts)
    }

    /// parse a vector of address=>(storage,balance,code,nonce) entry
    fn parse_accounts_post(
        &mut self,
        accounts_post: &HashMap<String, AccountPost>,
    ) -> Result<HashMap<Address, AccountMatch>> {
        let mut accounts = HashMap::new();
        for (address, acc) in accounts_post {
            let address = Self::parse_address(address)?;
            let mut storage: HashMap<U256, U256> = HashMap::new();
            if let Some(acc_storage) = &acc.storage {
                for (k, v) in acc_storage {
                    storage.insert(Self::parse_u256(k)?, Self::parse_u256(v)?);
                }
            }
            let account = AccountMatch {
                address,
                balance: acc
                    .balance
                    .as_ref()
                    .map(|v| Self::parse_u256(v))
                    .transpose()?,
                code: acc.code.as_ref().map(|v| self.parse_code(v)).transpose()?,
                nonce: acc
                    .nonce
                    .as_ref()
                    .map(|v| Self::parse_u256(v))
                    .transpose()?,
                storage,
            };
            accounts.insert(address, account);
        }
        Ok(accounts)
    }

    /// converts list of tagged values string into a map
    /// if there's no tags, an entry with an empty tag and the full string is
    /// returned
    fn decompose_tags(expr: &str) -> HashMap<String, String> {
        let mut tags = HashMap::new();
        let mut it = expr.trim();
        if it.is_empty() {
            tags.insert("".to_string(), "".to_string());
        } else {
            while !it.is_empty() {
                if it.starts_with(':') {
                    let tag = &it[..it.find(&[' ', '\n']).expect("unable to find end tag")];
                    it = &it[tag.len() + 1..];
                    let value_len = if tag == ":yul" || tag == ":solidity" || tag == ":asm" {
                        it.len()
                    } else {
                        it.find(':').unwrap_or(it.len())
                    };
                    tags.insert(tag.to_string(), it[..value_len].trim().to_string());
                    it = &it[value_len..];
                } else {
                    tags.insert("".to_string(), it.trim().to_string());
                    it = &it[it.len()..]
                }
            }
        }
        tags
    }
    /// returns the element as an address
    fn parse_address(as_str: &str) -> Result<Address> {
        if let Some(hex) = as_str.strip_prefix("0x") {
            Ok(Address::from_slice(
                &hex::decode(hex).context("parse_address")?,
            ))
        } else {
            Ok(Address::from_slice(
                &hex::decode(as_str).context("parse_address")?,
            ))
        }
    }

    /// returns the element as a to address
    fn parse_to_address(as_str: &str) -> Result<Option<Address>> {
        if as_str.trim().is_empty() {
            return Ok(None);
        }
        Self::parse_address(as_str).map(|x| Ok(Some(x)))?
    }

    /// returns the element as an array of bytes
    fn parse_bytes(as_str: &str) -> Result<Bytes> {
        if let Some(hex) = as_str.strip_prefix("0x") {
            Ok(Bytes::from(hex::decode(hex).context("parse_bytes")?))
        } else {
            Ok(Bytes::from(hex::decode(as_str).context("parse_bytes")?))
        }
    }

    /// parse entry as code, can be 0x, :raw or { LLL }
    fn parse_code(&mut self, as_str: &str) -> Result<Bytes> {
        let tags = Self::decompose_tags(as_str);

        let mut code = if let Some(notag) = tags.get("") {
            if notag.starts_with("0x") {
                Bytes::from(hex::decode(&tags[""][2..]).context("parse_code")?)
            } else if notag.starts_with('{') {
                self.compiler.lll(notag)?
            } else if notag.trim().is_empty() {
                Bytes::default()
            } else {
                bail!(
                    "do not know what to do with code(1) {:?} '{}'",
                    as_str,
                    notag
                );
            }
        } else if let Some(raw) = tags.get(":raw") {
            Bytes::from(hex::decode(&raw[2..])?)
        } else if let Some(yul) = tags.get(":yul") {
            self.compiler.yul(yul)?
        } else if let Some(solidity) = tags.get(":solidity") {
            self.compiler.solidity(solidity)?
        } else if let Some(asm) = tags.get(":asm") {
            self.compiler.asm(asm)?
        } else {
            bail!("do not know what to do with code(2) '{:?}'", as_str);
        };

        // TODO: remote the finish with STOP if does not finish with it when fixed
        if !code.0.is_empty() && code.0[code.0.len() - 1] != OpcodeId::STOP.as_u8() {
            let mut code_stop = Vec::new();
            code_stop.extend_from_slice(&code.0);
            code_stop.push(OpcodeId::STOP.as_u8());
            code = Bytes::from(code_stop);
        }

        Ok(code)
    }

    /// returns the element as calldata bytes, supports :raw and :abi
    fn parse_calldata(&mut self, as_str: &str) -> Result<Bytes> {
        let tags = Self::decompose_tags(as_str);

        if let Some(notag) = tags.get("") {
            let notag = notag.trim();
            if notag.is_empty() {
                Ok(Bytes::default())
            } else if notag.starts_with('{') {
                Ok(self.compiler.lll(notag)?)
            } else if let Some(hex) = notag.strip_prefix("0x") {
                Ok(Bytes::from(hex::decode(hex)?))
            } else {
                bail!("do not know what to do with calldata (1): '{:?}'", as_str);
            }
        } else if let Some(raw) = tags.get(":raw") {
            Ok(Bytes::from(hex::decode(&raw[2..])?))
        } else if let Some(abi) = tags.get(":abi") {
            Ok(abi::encode_funccall(abi)?)
        } else if let Some(yul) = tags.get(":yul") {
            Ok(self.compiler.yul(yul)?)
        } else {
            bail!(
                "do not know what to do with calldata: (2) {:?} '{:?}'",
                tags,
                as_str
            )
        }
    }

    /// parse a hash entry
    fn parse_hash(value: &str) -> Result<H256> {
        if let Some(hex) = value.strip_prefix("0x") {
            Ok(H256::from_slice(&hex::decode(hex).context("parse_hash")?))
        } else {
            Ok(H256::from_slice(&hex::decode(value).context("parse_hash")?))
        }
    }

    /// parse an uint256 entry
    fn parse_u256(as_str: &str) -> Result<U256> {
        if let Some(stripped) = as_str.strip_prefix("0x") {
            Ok(U256::from_str_radix(stripped, 16)?)
        } else if as_str
            .to_lowercase()
            .contains(['a', 'b', 'c', 'd', 'e', 'f'])
        {
            Ok(U256::from_str_radix(as_str, 16)?)
        } else {
            Ok(U256::from_str_radix(as_str, 10)?)
        }
    }

    /// parse u64 entry
    #[allow(clippy::cast_sign_loss)]
    fn parse_u64(as_str: &str) -> Result<u64> {
        if let Some(stripped) = as_str.strip_prefix("0x") {
            Ok(U256::from_str_radix(stripped, 16)?.as_u64())
        } else {
            Ok(U256::from_str_radix(as_str, 10)?.as_u64())
        }
    }

    /// parse a unique or a list of references,
    ///   -1 => Ref::Any
    ///   a int value => Ref::Index(value)
    ///   :label xxx => Ref::Label(value)
    ///   <range_lo>-<range_hi> >= Ref::Index(range_lo)..=RefIndex(range_hi)
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    fn parse_refs(value: &serde_json::Value) -> Result<Refs> {
        let mut refs = Vec::new();
        if let Some(index) = value.as_i64() {
            if index == -1 {
                refs.push(Ref::Any);
            } else {
                refs.push(Ref::Index(index as usize));
            }
        } else if let Some(array) = value.as_array() {
            for element in array {
                if let Some(index) = element.as_u64() {
                    refs.push(Ref::Index(index as usize));
                } else {
                    bail!("unable to parse ref: {:?}", value);
                }
            }
        } else {
            bail!("unable to parse ref(2): {:?}", value);
        }
        Ok(Refs(refs))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const JSON: &str = r#"
{
    "add11" : {
        "_info" : {
            "comment" : "A test for (add 1 1) opcode result"
        },
        "env" : {
            "currentCoinbase" : "2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",
            "currentDifficulty" : "0x20000",
            "currentGasLimit" : "0xFF112233445566",
            "currentNumber" : "1",
            "currentTimestamp" : "1000",
            "previousHash" : "5e20a0453cecd065ea59c37ac63e079ee08998b6045136a8ce6635c7912ec0b6"
        },
        "expect" : [
            {
                "indexes" : {
                    "data" : -1,
                    "gas" : -1,
                    "value" : -1
                },
                "network" : [">=Berlin"],
                "result" : {
                    "095e7baea6a6c7c4c2dfeb977efac326af552d87" : {
                        "code" : "0x600160010160005500",
                        "nonce" : "1",
                        "storage" : {
                            "0x00" : "0x02"
                        }
                    }
                }
            }
        ],
        "pre" : {
            "095e7baea6a6c7c4c2dfeb977efac326af552d87" : {
                "balance" : "1000000000000000000",
                "code" : "0x600160010160005500",
                "nonce" : "0",
                "storage" : {
                }
            }
        },
        "transaction" : {
            "data" : [
                "0x6001",
                "0x6002"
            ],
            "gasLimit" : [
                "400000"
            ],
            "gasPrice" : "10",
            "nonce" : "0",
            "secretKey" : "45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8",
            "to" : "095e7baea6a6c7c4c2dfeb977efac326af552d87",
            "value" : [
                "100000"
            ]
        }
    }
}
"#;
    #[test]
    fn test_json_parse() -> Result<()> {
        let mut compiler = Compiler::new(true, None)?;
        let mut builder = JsonStateTestBuilder::new(&mut compiler);
        let test = builder.load_json("test_path", JSON)?.remove(0);

        let acc095e = Address::from_str("0x095e7baea6a6c7c4c2dfeb977efac326af552d87")?;

        let expected = StateTest {
            path: "test_path".to_string(),
            id: "add11_d0_g0_v0".to_string(),
            env: Env {
                current_coinbase: Address::from_str("0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba")?,
                current_difficulty: U256::from(131072u64),
                current_gas_limit: 0xFF112233445566,
                current_number: 1,
                current_timestamp: 1000,
                previous_hash: H256::from_str(
                    "0x5e20a0453cecd065ea59c37ac63e079ee08998b6045136a8ce6635c7912ec0b6",
                )?,
            },
            secret_key: Bytes::from(hex::decode(
                "45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8",
            )?),
            from: Address::from_str("0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b")?,
            to: Some(Address::from_str(
                "0x095e7baea6a6c7c4c2dfeb977efac326af552d87",
            )?),
            gas_limit: 400000,
            gas_price: U256::from(10u64),
            nonce: U256::from(0u64),
            value: U256::from(100000u64),
            data: Bytes::from(hex::decode("6001")?),
            pre: HashMap::from([(
                acc095e,
                Account {
                    address: acc095e,
                    nonce: U256::from(0u64),
                    balance: U256::from(1000000000000000000u64),
                    code: Bytes::from(hex::decode("600160010160005500")?),
                    storage: HashMap::new(),
                },
            )]),
            result: HashMap::from([(
                acc095e,
                AccountMatch {
                    address: acc095e,
                    nonce: Some(U256::from(1u64)),
                    balance: None,
                    code: Some(Bytes::from(hex::decode("600160010160005500")?)),
                    storage: HashMap::from([(U256::zero(), U256::from(2u64))]),
                },
            )]),
            exception: false,
        };

        assert_eq!(expected, test);

        Ok(())
    }
}
