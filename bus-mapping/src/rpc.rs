//! Module which contains all the RPC calls that are needed at any point to
//! query a Geth node in order to get a Block, Tx or Trace info.

use crate::eth_types::{
    Block, GethExecTrace, Hash, ResultGethExecTraces, Transaction, U64,
};
use crate::Error;
use ethers_providers::JsonRpcClient;

/// Serialize a type.
///
/// # Panics
///
/// If the type returns an error during serialization.
pub fn serialize<T: serde::Serialize>(t: &T) -> serde_json::Value {
    serde_json::to_value(t).expect("Types never fail to serialize.")
}

/// Struct used to define the input that you want to provide to the
/// `eth_getBlockByNumber` call as it mixes numbers with string literals.
#[derive(Debug)]
pub enum BlockNumber {
    /// Specific block number
    Num(U64),
    /// Earliest block
    Earliest,
    /// Latest block
    Latest,
    /// Pending block
    Pending,
}

impl From<u64> for BlockNumber {
    fn from(num: u64) -> Self {
        BlockNumber::Num(U64::from(num))
    }
}

impl BlockNumber {
    /// Serializes a BlockNumber as a [`Value`](serde_json::Value) to be able to
    /// throw it into a JSON-RPC request.
    pub fn serialize(self) -> serde_json::Value {
        match self {
            BlockNumber::Num(num) => serialize(&num),
            BlockNumber::Earliest => serialize(&"earliest"),
            BlockNumber::Latest => serialize(&"latest"),
            BlockNumber::Pending => serialize(&"pending"),
        }
    }
}

/// Placeholder structure designed to contain the methods that the BusMapping
/// needs in order to enable Geth queries.
pub struct GethClient<P: JsonRpcClient>(P);

impl<P: JsonRpcClient> GethClient<P> {
    /// Generates a new `GethClient` instance.
    pub fn new(provider: P) -> Self {
        Self(provider)
    }

    /// Calls `eth_getBlockByHash` via JSON-RPC returning a [`Block`] returning
    /// all the block information including it's transaction's details.
    pub async fn get_block_by_hash(
        &self,
        hash: Hash,
    ) -> Result<Block<Transaction>, Error> {
        let hash = serialize(&hash);
        let flag = serialize(&true);
        self.0
            .request("eth_getBlockByHash", [hash, flag])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))
    }

    /// Calls `eth_getBlockByNumber` via JSON-RPC returning a [`Block`]
    /// returning all the block information including it's transaction's
    /// details.
    pub async fn get_block_by_number(
        &self,
        block_num: BlockNumber,
    ) -> Result<Block<Transaction>, Error> {
        let num = block_num.serialize();
        let flag = serialize(&true);
        self.0
            .request("eth_getBlockByNumber", [num, flag])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))
    }

    /// Calls `debug_traceBlockByHash` via JSON-RPC returning a
    /// [`Vec<GethExecTrace>`] with each GethTrace corresponding to 1
    /// transaction of the block.
    pub async fn trace_block_by_hash(
        &self,
        hash: Hash,
    ) -> Result<Vec<GethExecTrace>, Error> {
        let hash = serialize(&hash);
        let resp: ResultGethExecTraces = self
            .0
            .request("debug_traceBlockByHash", [hash])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))?;
        Ok(resp.0.into_iter().map(|step| step.result).collect())
    }

    /// Calls `debug_traceBlockByNumber` via JSON-RPC returning a
    /// [`Vec<GethExecTrace>`] with each GethTrace corresponding to 1
    /// transaction of the block.
    pub async fn trace_block_by_number(
        &self,
        block_num: BlockNumber,
    ) -> Result<Vec<GethExecTrace>, Error> {
        let num = block_num.serialize();
        let resp: ResultGethExecTraces = self
            .0
            .request("debug_traceBlockByNumber", [num])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))?;
        Ok(resp.0.into_iter().map(|step| step.result).collect())
    }

    /// Calls `eth_getCode` via JSON-RPC returning a contract code
    pub async fn get_code_by_address(
        &self,
        contract_address: String,
    ) -> Result<String, Error> {
        self.0
            .request("eth_getCode", [contract_address, "0x2".to_string()])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))
    }
}

#[cfg(test)]
mod rpc_tests {
    use super::*;
    use ethers_providers::Http;
    use std::str::FromStr;
    use url::Url;

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_get_block_by_hash() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());

        let hash = Hash::from_str("0xe4f7aa19a76fcf31a6adff3b400300849e39dd84076765fb3af09d05ee9d787a").unwrap();
        let prov = GethClient::new(transport);
        let block_by_hash = prov.get_block_by_hash(hash).await.unwrap();
        assert!(hash == block_by_hash.hash.unwrap());
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_get_block_by_number() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());

        let hash = Hash::from_str("0xe4f7aa19a76fcf31a6adff3b400300849e39dd84076765fb3af09d05ee9d787a").unwrap();
        let prov = GethClient::new(transport);
        let block_by_num_latest =
            prov.get_block_by_number(BlockNumber::Latest).await.unwrap();
        assert!(hash == block_by_num_latest.hash.unwrap());
        let block_by_num = prov.get_block_by_number(1u64.into()).await.unwrap();
        assert!(
            block_by_num.transactions[0].hash
                == block_by_num_latest.transactions[0].hash
        );
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_trace_block_by_hash() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());

        let hash = Hash::from_str("0xe2d191e9f663a3a950519eadeadbd614965b694a65a318a0b8f053f2d14261ff").unwrap();
        let prov = GethClient::new(transport);
        let trace_by_hash = prov.trace_block_by_hash(hash).await.unwrap();
        // Since we called in the test block the same transaction twice the len
        // should be the same and != 0.
        assert!(
            trace_by_hash[0].struct_logs.len()
                == trace_by_hash[1].struct_logs.len()
        );
        assert!(!trace_by_hash[0].struct_logs.is_empty());
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_trace_block_by_number() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());
        let prov = GethClient::new(transport);
        let trace_by_hash = prov.trace_block_by_number(5.into()).await.unwrap();
        // Since we called in the test block the same transaction twice the len
        // should be the same and != 0.
        assert!(
            trace_by_hash[0].struct_logs.len()
                == trace_by_hash[1].struct_logs.len()
        );
        assert!(!trace_by_hash[0].struct_logs.is_empty());
    }

    #[ignore]
    #[tokio::test]
    async fn test_get_contract_code() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());
        let prov = GethClient::new(transport);
        let contract_address =
            "0xD5F110B3E81dE87F22Fa8c5e668a5Fc541c54E3d".to_string();
        let contract_code = "0x608060405234801561001057600080fd5b50600436106100415760003560e01c8063445df0ac146100465780638da5cb5b14610064578063fdacd576146100ae575b600080fd5b61004e6100dc565b6040518082815260200191505060405180910390f35b61006c6100e2565b604051808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b6100da600480360360208110156100c457600080fd5b8101908080359060200190929190505050610107565b005b60015481565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1681565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16146101ac576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260338152602001806101b76033913960400191505060405180910390fd5b806001819055505056fe546869732066756e6374696f6e206973207265737472696374656420746f2074686520636f6e74726163742773206f776e6572a265627a7a7231582007302f208a10686769509b529e1878bda1859883778d70dedd1844fe790c9bde64736f6c63430005100032".to_string();
        let gotten_contract_code =
            prov.get_code_by_address(contract_address).await.unwrap();
        assert_eq!(contract_code, gotten_contract_code);
    }
}
