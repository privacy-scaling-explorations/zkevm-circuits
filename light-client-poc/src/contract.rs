#![allow(dead_code)]
#![allow(unused_imports)]

use super::utils::MM;
use ethers::core::types::transaction::eip2930::AccessList;
use ethers::prelude::k256::ecdsa::SigningKey;
use ethers::prelude::k256::schnorr::signature::Verifier;
use ethers::prelude::k256::Secp256k1;
use ethers::providers::Middleware;
use ethers::solc;
use ethers::types::transaction::eip2930::AccessListItem;
use ethers::{
    middleware::SignerMiddleware,
    prelude::*,
    providers::{Http, Provider},
    signers::{LocalWallet, Signer},
    types::TransactionRequest,
    utils::format_units,
};
use eyre::Result;
use num_enum::IntoPrimitive;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::{convert::TryFrom, sync::Arc, time::Duration};

const SIMPLE_STORAGE_SOL : &str = r#"
// SPDX-License-Identifier: Unlicense
pragma solidity ^0.8.0;

contract SimpleStorage {
    constructor() payable {
        set(0xcafe, 0xbabe);
    }
    function get(uint k) view public returns (uint) {
       uint v;
       assembly {
           v := sload(k)
       }
       return v;
    }
    function set(uint k, uint v) payable public {
       assembly {
           sstore(k,v)
       }
    }
}
"#;

abigen!(
    SimpleStorage,
    r"[
    function get(uint k) view returns (uint)
    function set(uint k, uint v) public
]"
);

pub(crate) struct Contract {
    pub contract: SimpleStorage<MM>,
    pub receipt: TransactionReceipt,
}

impl Contract {
    pub async fn deploy(client: Arc<MM>) -> Result<Self> {
        let contract = "SimpleStorage";

        let mut path = std::env::temp_dir();
        path.push("SimpleStorage.sol");

        std::fs::write(&path, SIMPLE_STORAGE_SOL)?;

        // compile it

        let compiler_input = CompilerInput::new(path)?
            .remove(0)
            .evm_version(EvmVersion::Paris);
        let compiled = Solc::default().compile_exact(&compiler_input)?;

        let (abi, bytecode, _runtime_bytecode) = compiled
            .find(contract)
            .expect("could not find contract")
            .into_parts_or_default();

        println!("deploying contract");

        let factory = ContractFactory::new(abi.clone(), bytecode.clone(), client.clone());
        let deployer = factory.deploy(())?.legacy();

        let (contract, receipt) = deployer.send_with_receipt().await?;

        let address = contract.address();

        let contract = SimpleStorage::new(address, client.clone());

        Ok(Self { contract, receipt })
    }

    pub async fn get(&self, key: U256) -> Result<U256> {
        let value = self.contract.get(key).call().await?;
        Ok(value)
    }

    pub async fn set(&self, key: U256, value: U256) -> Result<TransactionReceipt> {
        let tx: TransactionReceipt = self
            .contract
            .set(key, value)
            .legacy()
            .send()
            .await?
            .await?
            .unwrap();
        Ok(tx)
    }
}
