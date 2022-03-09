use super::lllc::Lllc;
use crate::statetest::{Env, PartialAccount, StateTest};
use anyhow::{bail, Context, Result};
use eth_types::{geth_types::Account, Address, Bytes, H256, U256};
use ethers_core::utils::secret_key_to_address;
use k256::ecdsa::SigningKey;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::HashMap;
use std::convert::TryInto;
use yaml_rust::Yaml;

static TAGS_REGEXP: Lazy<Regex> = Lazy::new(|| Regex::new("((:[a-z]+ )([^:]+))").unwrap());

type Tag = String;
type Label = String;

#[derive(Debug, Clone)]
enum Ref {
    Any,
    Index(usize),
    Label(String),
}

struct Refs(Vec<Ref>);

impl Refs {
    fn contains_index(&self, idx: usize) -> bool {
        self.0.iter().any(|r| match r {
            Ref::Index(i) => i == &idx,
            Ref::Label(_) => false,
            Ref::Any => true,
        })
    }
    fn contains_label(&self, lbl: &str) -> bool {
        self.0.iter().any(|r| match r {
            Ref::Index(_) => false,
            Ref::Label(l) => l == lbl,
            Ref::Any => true,
        })
    }
}

pub struct YamlStateTestBuilder {
    lllc: Lllc,
}

impl YamlStateTestBuilder {
    pub fn new(lllc: Lllc) -> Self {
        Self { lllc }
    }

    /// generates `StateTest` vectors from a ethereum yaml test specification
    pub fn from_yaml(&mut self, source: &str) -> Result<Vec<StateTest>> {
        // get the yaml root element
        let doc = yaml_rust::YamlLoader::load_from_str(source)?
            .into_iter()
            .next()
            .context("get yaml doc")?;

        // collect test names, that are the top-level items in the yaml doc
        let test_names: Vec<_> = doc
            .as_hash()
            .context("parse_hash")?
            .keys()
            .map(|v| v.as_str().context("as_str"))
            .collect::<Result<_>>()?;

        // for each test defined in the yaml, create the according defined tests
        let mut tests = Vec::new();
        for test_name in test_names {
            let yaml_test = &doc[test_name];

            // parse env
            let env = Self::parse_env(&yaml_test["env"])?;

            // parse pre (account states before executing the transaction)
            // [TODO] remove ugly unwrap here
            let pre: HashMap<Address, Account> = self
                .parse_accounts(&yaml_test["pre"])?
                .into_iter()
                .map(|(addr, account)| (addr, account.try_into().unwrap()))
                .collect();

            // parse transaction
            let yaml_transaction = &yaml_test["transaction"];
            let data_s: Vec<_> = yaml_transaction["data"]
                .as_vec()
                .context("as_vec")?
                .iter()
                .map(Self::parse_calldata)
                .collect::<Result<_>>()?;

            let gas_limit_s: Vec<_> = yaml_transaction["gasLimit"]
                .as_vec()
                .context("as_vec")?
                .iter()
                .map(Self::parse_u64)
                .collect::<Result<_>>()?;

            let value_s: Vec<_> = yaml_transaction["value"]
                .as_vec()
                .context("as_vec")?
                .iter()
                .map(Self::parse_u256)
                .collect::<Result<_>>()?;

            let gas_price = Self::parse_u256(&yaml_transaction["gasPrice"])?;
            let nonce = Self::parse_u256(&yaml_transaction["nonce"])?;
            let to = Self::parse_address(&yaml_transaction["to"])?;
            let secret_key = Self::parse_bytes(&yaml_transaction["secretKey"])?;
            let from = secret_key_to_address(&SigningKey::from_bytes(&secret_key.to_vec())?);

            // parse expects (account states before executing the transaction)
            let mut expects = Vec::new();
            for expect in yaml_test["expect"].as_vec().context("as_vec")?.iter() {
                let data_refs = Self::parse_refs(&expect["indexes"]["data"])?;
                let gparse_refs = Self::parse_refs(&expect["indexes"]["gas"])?;
                let value_refs = Self::parse_refs(&expect["indexes"]["value"])?;
                let result = self.parse_accounts(&expect["result"])?;
                expects.push((data_refs, gparse_refs, value_refs, result));
            }

            // generate all the tests defined in the transaction by generating product of
            // data x gas x value
            for (idx_data, data) in data_s.iter().enumerate() {
                for (idx_gas, gas_limit) in gas_limit_s.iter().enumerate() {
                    for (idx_value, value) in value_s.iter().enumerate() {
                        // find the first result that fulfills the pattern
                        for (data_refs, parse_refs, value_refs, result) in &expects {
                            // check if this result can be applied to the current test
                            let mut data_label = String::new();
                            if let Some(label) = &data.1 {
                                if !data_refs.contains_label(label) {
                                    continue;
                                }
                                data_label = format!("({})", label);
                            } else if !data_refs.contains_index(idx_data) {
                                continue;
                            }

                            if !parse_refs.contains_index(idx_gas) {
                                continue;
                            }

                            if !value_refs.contains_index(idx_value) {
                                continue;
                            }

                            // add the test
                            tests.push(StateTest {
                                id: format!(
                                    "{}_d{}{}_g{}_v{}",
                                    test_name, idx_data, data_label, idx_gas, idx_value
                                ),
                                env: env.clone(),
                                pre: pre.clone(),
                                result: result.clone(),
                                from,
                                secret_key: secret_key.clone(),
                                to: Some(to),
                                gas_limit: *gas_limit,
                                gas_price,
                                nonce,
                                value: *value,
                                data: data.0.clone(),
                            });
                            break;
                        }
                    }
                }
            }
        }

        Ok(tests)
    }

    /// parse env section
    fn parse_env(yaml: &Yaml) -> Result<Env> {
        Ok(Env {
            current_coinbase: Self::parse_address(&yaml["currentCoinbase"])?,
            current_difficulty: Self::parse_u256(&yaml["currentDifficulty"])?,
            current_gas_limit: Self::parse_u64(&yaml["currentGasLimit"])?,
            current_number: Self::parse_u64(&yaml["currentNumber"])?,
            current_timestamp: Self::parse_u64(&yaml["currentTimestamp"])?,
            previous_hash: Self::parse_hash(&yaml["previousHash"])?,
        })
    }

    /// parse a vector of address=>(storage,balance,code,nonce) entry
    fn parse_accounts(&mut self, yaml: &Yaml) -> Result<HashMap<Address, PartialAccount>> {
        let mut accounts = HashMap::new();
        for (address, account) in yaml.as_hash().context("parse_hash")?.iter() {
            let acc_storage = &account["storage"];
            let acc_balance = &account["balance"];
            let acc_code = &account["code"];
            let acc_nonce = &account["nonce"];

            let mut storage = HashMap::new();
            if !acc_storage.is_badvalue() {
                for (slot, value) in account["storage"].as_hash().context("parse_hash")?.iter() {
                    storage.insert(Self::parse_u256(slot)?, Self::parse_u256(value)?);
                }
            }

            let address = Self::parse_address(address)?;
            let account = PartialAccount {
                address,
                balance: if acc_balance.is_badvalue() {
                    None
                } else {
                    Some(Self::parse_u256(acc_balance)?)
                },
                code: if acc_code.is_badvalue() {
                    None
                } else {
                    Some(self.parse_code(acc_code)?)
                },
                nonce: if acc_nonce.is_badvalue() {
                    None
                } else {
                    Some(Self::parse_u256(acc_nonce)?)
                },
                storage,
            };
            accounts.insert(address, account);
        }
        Ok(accounts)
    }

    /// converts list of tagged values string into a map
    /// if there's no tags, an entry with an empty tag and the full string is
    /// returned
    fn decompose_tags(expr: &str) -> HashMap<Tag, String> {
        let expr = expr.trim();
        if expr.starts_with(':') {
            TAGS_REGEXP
                .captures_iter(expr)
                .map(|cap| (cap[2].trim().into(), cap[3].trim().into()))
                .collect()
        } else {
            let mut tags = HashMap::new();
            tags.insert("".to_string(), expr.to_string());
            tags
        }
    }

    /// returns the element as an address
    fn parse_address(yaml: &Yaml) -> Result<Address> {
        if let Some(as_str) = yaml.as_str() {
            Ok(Address::from_slice(&hex::decode(as_str)?))
        } else if let Some(as_i64) = yaml.as_i64() {
            let hex = format!("{:0>40}", as_i64);
            Ok(Address::from_slice(&hex::decode(hex)?))
        } else {
            bail!("cannot address");
        }
    }

    /// returns the element as an array of bytes
    fn parse_bytes(yaml: &Yaml) -> Result<Bytes> {
        let mut as_str = yaml.as_str().context("as_str")?;
        if let Some(stripped) = as_str.strip_prefix("0x") {
            as_str = stripped;
        }
        Ok(Bytes::from(hex::decode(as_str)?))
    }

    /// returns the element as calldata bytes, supports :raw and :abi
    fn parse_calldata(yaml: &Yaml) -> Result<(Bytes, Option<Label>)> {
        let tags = Self::decompose_tags(yaml.as_str().context("as_str")?);
        let label = tags.get(":label").cloned();

        if let Some(raw) = tags.get(":raw") {
            Ok((Bytes::from(hex::decode(&raw[2..])?), label))
        } else if let Some(abi) = tags.get(":abi") {
            Ok((Self::encode_abi_funccall(abi)?, label))
        } else {
            bail!("do not know what to do with calldata")
        }
    }

    /// encodes an abi call (e.g. "f(uint) 1")
    pub fn encode_abi_funccall(spec: &str) -> Result<Bytes> {
        use ethers_core::abi::{Function, Param, ParamType, StateMutability, Token};

        // split parts into `func_name` ([`func_params`]) `args`

        let tokens: Vec<_> = spec.split(' ').collect();
        let func = tokens[0];
        let args = &tokens[1..];

        let func_name_params: Vec<_> = func.split([',', '(', ')']).collect();
        let func_name = func_name_params[0];
        let func_params = &func_name_params[1..func_name_params.len() - 1];

        // transform func_params and args into the appropiate types

        let map_type = |t| match t {
            "uint" => ParamType::Uint(256),
            _ => unimplemented!(),
        };

        let encode_type = |t, v| match t {
            &ParamType::Uint(256) => U256::from_str_radix(v, 10).map(Token::Uint),
            _ => unimplemented!(),
        };

        let func_params: Vec<_> = func_params
            .iter()
            .enumerate()
            .map(|(n, t)| Param {
                name: format!("p{}", n),
                kind: map_type(t),
                internal_type: None,
            })
            .collect();

        let args: Vec<Token> = func_params
            .iter()
            .zip(args)
            .map(|(typ, val)| encode_type(&typ.kind, val))
            .collect::<std::result::Result<_, _>>()?;

        // generate and return calldata

        #[allow(deprecated)]
        let func = Function {
            name: func_name.to_string(),
            inputs: func_params,
            outputs: vec![],
            state_mutability: StateMutability::Payable,
            constant: false,
        };

        Ok(Bytes::from(func.encode_input(&args)?))
    }

    // parse entry as code, can be 0x, :raw or { LLL }
    fn parse_code(&mut self, yaml: &Yaml) -> Result<Bytes> {
        let tags = Self::decompose_tags(yaml.as_str().context("not an str")?);

        if let Some(notag) = tags.get("") {
            if notag.starts_with("0x") {
                Ok(Bytes::from(hex::decode(&tags[""][2..])?))
            } else if notag.starts_with('{') {
                let code = notag.trim_start_matches('{').trim_end_matches('}').trim();
                self.lllc.compile(code)
            } else {
                bail!("do not know what to do with code");
            }
        } else if let Some(raw) = tags.get(":raw") {
            Ok(Bytes::from(hex::decode(&raw[2..])?))
        } else {
            bail!("do not know what to do with code");
        }
    }

    // parse a hash entry
    fn parse_hash(yaml: &Yaml) -> Result<H256> {
        Ok(H256::from_slice(&hex::decode(
            yaml.as_str().context("not a str")?,
        )?))
    }

    // parse an uint256 entry
    fn parse_u256(yaml: &Yaml) -> Result<U256> {
        if let Some(as_int) = yaml.as_i64() {
            Ok(U256::from(as_int))
        } else if let Some(as_str) = yaml.as_str() {
            if let Some(stripped) = as_str.strip_prefix("0x") {
                Ok(U256::from_str_radix(stripped, 16)?)
            } else {
                Ok(U256::from_str_radix(as_str, 10)?)
            }
        } else {
            bail!("{:?}", yaml)
        }
    }

    // parse u64 entry
    #[allow(clippy::cast_sign_loss)]
    fn parse_u64(yaml: &Yaml) -> Result<u64> {
        if let Some(as_int) = yaml.as_i64() {
            Ok(as_int as u64)
        } else if let Some(as_str) = yaml.as_str() {
            if let Some(stripped) = as_str.strip_prefix("0x") {
                Ok(U256::from_str_radix(stripped, 16)?.as_u64())
            } else {
                Ok(U256::from_str_radix(as_str, 10)?.as_u64())
            }
        } else {
            bail!("{:?}", yaml)
        }
    }

    // parse a unique or a list of references,
    //   -1 => Ref::Any
    //   a int value => Ref::Index(value)
    //   :label xxx => Ref::Label(value)
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    fn parse_refs(yaml: &Yaml) -> Result<Refs> {
        // convert a unique element into a list
        let yamls = if yaml.is_array() {
            yaml.as_vec().context("as_vec")?.iter().collect()
        } else {
            vec![yaml]
        };

        let mut refs = Vec::new();

        for yaml in yamls {
            let r = if let Some(as_int) = yaml.as_i64() {
                // index or any
                if as_int == -1 {
                    Ref::Any
                } else {
                    Ref::Index(as_int as usize)
                }
            } else if let Some(as_str) = yaml.as_str() {
                // label
                let tags = Self::decompose_tags(as_str);
                if let Some(label) = tags.get(":label") {
                    Ref::Label(label.to_string())
                } else {
                    bail!("{:?}", yaml);
                }
            } else {
                bail!("{:?}", yaml);
            };
            refs.push(r);
        }
        Ok(Refs(refs))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::statetest::StateTestError;
    use eth_types::address;

    const TEMPLATE: &str = r#"
arith:
  env:
    currentCoinbase: 2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
    currentDifficulty: 0x20000
    currentGasLimit: 100000000
    currentNumber: 1
    currentTimestamp: 1000
    previousHash: 5e20a0453cecd065ea59c37ac63e079ee08998b6045136a8ce6635c7912ec0b6
  pre:
    cccccccccccccccccccccccccccccccccccccccc:
      balance: 1000000000000
      code: :raw 0x6001
      nonce: '0'
      storage:
        0 : 0x01
    a94f5374fce5edbc8e2a8697c15331677e6ebf0b:
      balance: 1000000000000
      code: '0x'
      nonce: '0'
      storage: {}
  transaction:
    data:
    - :raw 0x00
    - :label data1 :raw 0x01
    gasLimit:
    - '80000000'
    - '80000001'
    gasPrice: '10'
    nonce: '0'
    to: cccccccccccccccccccccccccccccccccccccccc
    value:
    - '1'
    - '2'
    secretKey: "45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8"
  expect:
    - indexes:
        data: :label data1
        gas:  !!int 1
        value: !!int 1
      network:
        - '>=Istanbul'
      result:
        cccccccccccccccccccccccccccccccccccccccc:
          balance: 10

    - indexes:
        data: !!int -1
        gas:  !!int 1
        value: !!int -1
      network:
        - '>=Istanbul'
      result:
        cccccccccccccccccccccccccccccccccccccccc:
          balance: 20

    - indexes:
        data: !!int -1
        gas:  !!int -1
        value: !!int 1
      network:
        - '>=Istanbul'
      result:
        cccccccccccccccccccccccccccccccccccccccc:
          balance: 30

    - indexes:
        data: !!int -1
        gas:  !!int -1
        value: !!int -1
      network:
        - '>=Istanbul'
      result:
        cccccccccccccccccccccccccccccccccccccccc:
          storage:
            # 17^9
            0: {{ storage }}
          balance: {{ balance }}
          nonce: {{ nonce }}
          code: {{ code }}
"#;

    #[test]
    fn test_abi_encoding() -> Result<()> {
        // [TODO] does not match with
        // https://github.com/ethereum/tests/blob/0e8d25bb613cab7f9e99430f970e1e6cbffdbf1a/GeneralStateTests/VMTests/vmArithmeticTest/add.json#L244
        assert_eq!(
            hex::encode(YamlStateTestBuilder::encode_abi_funccall("f(uint) 4")?),
            "b3de648b0000000000000000000000000000000000000000000000000000000000000004"
        );
        Ok(())
    }

    #[test]
    fn test_combinations() -> Result<()> {
        let tcs = YamlStateTestBuilder::new(Lllc::default())
            .from_yaml(
                &TEMPLATE
                    .replace("{{ storage }}", "0x01")
                    .replace("{{ balance }}", "40")
                    .replace("{{ code }}", ":raw 0x6001")
                    .replace("{{ nonce }}", "0"),
            )?
            .into_iter()
            .map(|v| (v.id.clone(), v))
            .collect::<HashMap<_, _>>();

        assert_eq!(tcs.len(), 8);

        let ccccc = address!("cccccccccccccccccccccccccccccccccccccccc");
        let check = |id: &str, v: u64| {
            assert_eq!(
                tcs[id].result[&ccccc].balance,
                Some(U256::from(v)),
                "{}",
                id
            )
        };

        check("arith_d0_g0_v0", 40);
        check("arith_d1(data1)_g1_v1", 10);
        check("arith_d0_g1_v0", 20);
        check("arith_d0_g0_v1", 30);
        Ok(())
    }

    #[test]
    fn test_parse() -> Result<()> {
        let mut tc = YamlStateTestBuilder::new(Lllc::default()).from_yaml(
            &TEMPLATE
                .replace("{{ storage }}", "0x01")
                .replace("{{ balance }}", "1000000000000")
                .replace("{{ code }}", ":raw 0x6001")
                .replace("{{ nonce }}", "0"),
        )?;
        let current = tc.remove(0);

        let a94f5 = address!("a94f5374fce5edbc8e2a8697c15331677e6ebf0b");
        let ccccc = address!("cccccccccccccccccccccccccccccccccccccccc");

        let expected = StateTest {
            id: "arith_d0_g0_v0".into(),
            env: Env {
                current_coinbase: address!("0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"),
                current_difficulty: U256::from(0x20000u64),
                current_number: 1,
                current_timestamp: 1000,
                current_gas_limit: 100000000,
                previous_hash: H256::from_slice(&hex::decode(
                    "5e20a0453cecd065ea59c37ac63e079ee08998b6045136a8ce6635c7912ec0b6",
                )?),
            },
            secret_key: Bytes::from(hex::decode(
                "45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8",
            )?),
            from: a94f5.clone(),
            to: Some(ccccc.clone()),
            gas_limit: 80000000,
            gas_price: U256::from(10u64),
            nonce: U256::zero(),
            value: U256::one(),
            data: Bytes::from(&[0]),
            pre: HashMap::from([
                (
                    ccccc.clone(),
                    Account {
                        address: ccccc.clone(),
                        balance: U256::from(1000000000000u64),
                        code: Bytes::from(&[0x60, 0x01]),
                        nonce: U256::zero(),
                        storage: HashMap::from([(U256::zero(), U256::one())]),
                    },
                ),
                (
                    a94f5.clone(),
                    Account {
                        address: a94f5.clone(),
                        balance: U256::from(1000000000000u64),
                        code: Bytes::default(),
                        nonce: U256::zero(),
                        storage: HashMap::new(),
                    },
                ),
            ]),
            result: HashMap::from([(
                ccccc.clone(),
                PartialAccount {
                    address: ccccc.clone(),
                    balance: Some(U256::from(1000000000000u64)),
                    nonce: Some(U256::from(0)),
                    code: Some(Bytes::from(&[0x60, 0x01])),
                    storage: HashMap::from([(U256::zero(), U256::one())]),
                },
            )]),
        };

        assert_eq!(current, expected);
        Ok(())
    }

    #[test]
    fn test_result_pass() -> Result<()> {
        let mut tc = YamlStateTestBuilder::new(Lllc::default()).from_yaml(
            &TEMPLATE
                .replace("{{ storage }}", "0x01")
                .replace("{{ balance }}", "1000000000000")
                .replace("{{ code }}", ":raw 0x6001")
                .replace("{{ nonce }}", "0"),
        )?;
        tc.remove(0).run()?;
        Ok(())
    }
    #[test]
    fn test_result_bad_storage() -> Result<()> {
        let mut tc = YamlStateTestBuilder::new(Lllc::default()).from_yaml(
            &TEMPLATE
                .replace("{{ storage }}", "0x02")
                .replace("{{ balance }}", "1000000000000")
                .replace("{{ code }}", ":raw 0x6001")
                .replace("{{ nonce }}", "0"),
        )?;

        assert_eq!(
            tc.remove(0).run(),
            Err(StateTestError::StorageMismatch {
                slot: U256::from(0u8),
                expected: U256::from(2u8),
                found: Some(U256::from(1u8))
            })
        );

        Ok(())
    }
    #[test]
    fn test_result_bad_balance() -> Result<()> {
        let mut tc = YamlStateTestBuilder::new(Lllc::default()).from_yaml(
            &TEMPLATE
                .replace("{{ storage }}", "0x02")
                .replace("{{ balance }}", "1000000000001")
                .replace("{{ code }}", ":raw 0x6001")
                .replace("{{ nonce }}", "0"),
        )?;

        assert_eq!(
            tc.remove(0).run(),
            Err(StateTestError::BalanceMismatch {
                expected: U256::from(1000000000001u64),
                found: U256::from(1000000000000u64)
            })
        );

        Ok(())
    }

    #[test]
    fn test_result_bad_code() -> Result<()> {
        let mut tc = YamlStateTestBuilder::new(Lllc::default()).from_yaml(
            &TEMPLATE
                .replace("{{ storage }}", "0x02")
                .replace("{{ balance }}", "1000000000000")
                .replace("{{ code }}", ":raw 0x6002")
                .replace("{{ nonce }}", "0"),
        )?;
        assert_eq!(
            tc.remove(0).run(),
            Err(StateTestError::CodeMismatch {
                expected: Bytes::from(&[0x60, 0x02]),
                found: Bytes::from(&[0x60, 0x01])
            })
        );

        Ok(())
    }

    #[test]
    fn test_result_bad_nonce() -> Result<()> {
        let mut tc = YamlStateTestBuilder::new(Lllc::default()).from_yaml(
            &TEMPLATE
                .replace("{{ storage }}", "0x02")
                .replace("{{ balance }}", "1000000000000")
                .replace("{{ code }}", ":raw 0x6001")
                .replace("{{ nonce }}", "2"),
        )?;

        assert_eq!(
            tc.remove(0).run(),
            Err(StateTestError::NonceMismatch {
                expected: U256::from(2),
                found: U256::from(0)
            })
        );

        Ok(())
    }
}
