//! Module which contains all the RPC calls that are needed at any point to
//! query a Geth node in order to get a Block, Tx or Trace info.

use std::time::Duration;

use crate::Error;
use eth_types::{
    Address, Block, Bytes, EIP1186ProofResponse, GethExecTrace, Hash, ResultGethExecTraces,
    Transaction, Word, U64,
};
pub use ethers_core::types::BlockNumber;
use ethers_providers::JsonRpcClient;
use serde::Serialize;

/// Serialize a type.
///
/// # Panics
///
/// If the type returns an error during serialization.
pub fn serialize<T: serde::Serialize>(t: &T) -> serde_json::Value {
    serde_json::to_value(t).expect("Types never fail to serialize.")
}

#[derive(Serialize)]
#[doc(hidden)]
pub(crate) struct GethLoggerConfig {
    /// enable memory capture
    #[serde(rename = "EnableMemory")]
    enable_memory: bool,
    /// disable stack capture
    #[serde(rename = "DisableStack")]
    disable_stack: bool,
    /// disable storage capture
    #[serde(rename = "DisableStorage")]
    disable_storage: bool,
    /// enable return data capture
    #[serde(rename = "EnableReturnData")]
    enable_return_data: bool,
}

impl Default for GethLoggerConfig {
    fn default() -> Self {
        Self {
            enable_memory: false,
            disable_stack: false,
            disable_storage: false,
            enable_return_data: true,
        }
    }
}

/// Placeholder structure designed to contain the methods that the BusMapping
/// needs in order to enable Geth queries.
pub struct GethClient<P: JsonRpcClient>(pub P);

impl<P: JsonRpcClient> GethClient<P> {
    /// Generates a new `GethClient` instance.
    pub fn new(provider: P) -> Self {
        Self(provider)
    }

    const REQUEST_TIMEOUT_1_MINUTE: Duration = Duration::from_secs(60);

    /// Calls `eth_coinbase` via JSON-RPC returning the coinbase of the network.
    pub async fn get_coinbase(&self) -> Result<Address, Error> {
        let method = "eth_coinbase";

        if let Ok(result) =
            tokio::time::timeout(Self::REQUEST_TIMEOUT_1_MINUTE, self.0.request(method, ())).await
        {
            match result {
                Ok(response) => {
                    let resp: Address = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `eth_chainId` via JSON-RPC returning the chain id of the network.
    pub async fn get_chain_id(&self) -> Result<u64, Error> {
        let method = "eth_chainId";

        if let Ok(result) =
            tokio::time::timeout(Self::REQUEST_TIMEOUT_1_MINUTE, self.0.request(method, ())).await
        {
            match result {
                Ok(response) => {
                    let resp: U64 = response;
                    Ok(resp.as_u64())
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `get_transaction_by_hash` via JSON-RPC returning a [`Transaction`]
    pub async fn get_transaction_by_hash(&self, hash: Hash) -> Result<Transaction, Error> {
        let hash = serialize(&hash);
        let method = "eth_getTransactionByHash";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [hash]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: Transaction = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `eth_getBlockByHash` via JSON-RPC returning a [`Block`] returning
    /// all the block information including it's transaction's details.
    pub async fn get_block_by_hash(&self, hash: Hash) -> Result<Block<Transaction>, Error> {
        let hash = serialize(&hash);
        let flag = serialize(&true);
        let method = "eth_getBlockByHash";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [hash, flag]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: Block<Transaction> = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `eth_getBlockByNumber` via JSON-RPC returning a [`Block`]
    /// returning all the block information including it's transaction's
    /// details.
    pub async fn get_block_by_number(
        &self,
        block_num: BlockNumber,
    ) -> Result<Block<Transaction>, Error> {
        let num = serialize(&block_num);
        let flag = serialize(&true);
        let method = "eth_getBlockByNumber";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [num, flag]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: Block<Transaction> = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `debug_traceBlockByHash` via JSON-RPC returning a
    /// [`Vec<GethExecTrace>`] with each GethTrace corresponding to 1
    /// transaction of the block.
    pub async fn trace_block_by_hash(&self, hash: Hash) -> Result<Vec<GethExecTrace>, Error> {
        let hash = serialize(&hash);
        let cfg = serialize(&GethLoggerConfig::default());
        let method = "debug_traceBlockByHash";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [hash, cfg]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: ResultGethExecTraces = response;
                    Ok(resp.0.into_iter().map(|step| step.result).collect())
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `debug_traceBlockByNumber` via JSON-RPC returning a
    /// [`Vec<GethExecTrace>`] with each GethTrace corresponding to 1
    /// transaction of the block.
    pub async fn trace_block_by_number(
        &self,
        block_num: BlockNumber,
    ) -> Result<Vec<GethExecTrace>, Error> {
        let num = serialize(&block_num);
        let cfg = serialize(&GethLoggerConfig::default());
        let method = "debug_traceBlockByNumber";
        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [num, cfg]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: ResultGethExecTraces = response;
                    Ok(resp.0.into_iter().map(|step| step.result).collect())
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `eth_getCode` via JSON-RPC returning a contract code
    pub async fn get_code(
        &self,
        contract_address: Address,
        block_num: BlockNumber,
    ) -> Result<Vec<u8>, Error> {
        let address = serialize(&contract_address);
        let num = serialize(&block_num);
        let method = "eth_getCode";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [address, num]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: Bytes = response;
                    Ok(resp.to_vec())
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `eth_getProof` via JSON-RPC returning a
    /// [`EIP1186ProofResponse`] returning the account and
    /// storage-values of the specified account including the Merkle-proof.
    pub async fn get_proof(
        &self,
        account: Address,
        keys: Vec<Word>,
        block_num: BlockNumber,
    ) -> Result<EIP1186ProofResponse, Error> {
        let account = serialize(&account);
        let keys = serialize(&keys);
        let num = serialize(&block_num);
        let method = "eth_getProof";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [account, keys, num]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp: EIP1186ProofResponse = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `miner_stop` via JSON-RPC, which makes the node stop mining
    /// blocks.  Useful for integration tests.
    pub async fn miner_stop(&self) -> Result<(), Error> {
        let method = "miner_stop";

        if let Ok(result) =
            tokio::time::timeout(Self::REQUEST_TIMEOUT_1_MINUTE, self.0.request(method, ())).await
        {
            match result {
                Ok(response) => {
                    let resp = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }

    /// Calls `miner_start` via JSON-RPC, which makes the node start mining
    /// blocks.  Useful for integration tests.
    pub async fn miner_start(&self) -> Result<(), Error> {
        let method = "miner_start";

        if let Ok(result) = tokio::time::timeout(
            Self::REQUEST_TIMEOUT_1_MINUTE,
            self.0.request(method, [serialize(&1)]),
        )
        .await
        {
            match result {
                Ok(response) => {
                    let resp = response;
                    Ok(resp)
                }
                Err(e) => Err(Error::JSONRpcError(e.into())),
            }
        } else {
            Err(Error::JSONRpcError(
                ethers_providers::ProviderError::CustomError(
                    format!("Timeout: {} no response in 60 seconds.", method).into(),
                ),
            ))
        }
    }
}

// Integration tests found in `integration-tests/tests/rpc.rs`.
