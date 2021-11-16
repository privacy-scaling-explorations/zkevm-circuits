//! Module which contains all the RPC calls that are needed at any point to query a Geth node in order to get a Block, Tx or Trace info.

use crate::eth_types::{Block, Hash, Transaction, U64};
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

/// Struct used to define the input that you want to provide to the `eth_getBlockByNumber` call as it mixes numbers with string literals.
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
    /// Serializes a BlockNumber as a [`Value`](serde_json::Value) to be able to throw it into a JSON-RPC request.
    pub fn serialize(self) -> serde_json::Value {
        match self {
            BlockNumber::Num(num) => serialize(&num),
            BlockNumber::Earliest => serialize(&"earliest"),
            BlockNumber::Latest => serialize(&"latest"),
            BlockNumber::Pending => serialize(&"pending"),
        }
    }
}

/// Placeholder structure designed to contain the methods that the BusMapping needs in order to enable Geth queries.
pub struct GethClient<P: JsonRpcClient>(P);

impl<P: JsonRpcClient> GethClient<P> {
    /// Generates a new `GethClient` instance.
    pub fn new(provider: P) -> Self {
        Self(provider)
    }

    /// Calls `eth_getBlockByHash` via JSON-RPC returning a [`Block`] returning all the block information including it's transaction's details.
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

    /// Calls `eth_getBlockByNumber` via JSON-RPC returning a [`Block`] returning all the block information including it's transaction's details.
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
}

#[cfg(test)]
mod rpc_tests {
    use super::*;
    use ethers_providers::Http;
    use std::str::FromStr;
    use url::Url;

    // The test is ignored as the values used depend on the Geth instance used each time you run the tests.
    // And we can't assume that everyone will have a Geth client synced with mainnet to have unified "test-vectors".
    //#[ignore]
    #[tokio::test]
    async fn test_get_block_by_hash() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());

        let hash = Hash::from_str("0x0492a44be5a74a6724bd666d308498c7a830a498f2c574768cbb25d09b4ec948").unwrap();
        let prov = GethClient::new(transport);
        let block_by_hash = prov.get_block_by_hash(hash).await.unwrap();
        assert!(hash == block_by_hash.hash.unwrap());
    }

    // The test is ignored as the values used depend on the Geth instance used each time you run the tests.
    // And we can't assume that everyone will have a Geth client synced with mainnet to have unified "test-vectors".
    //#[ignore]
    #[tokio::test]
    async fn test_get_block_by_number() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());

        let hash = Hash::from_str("0x0492a44be5a74a6724bd666d308498c7a830a498f2c574768cbb25d09b4ec948").unwrap();
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
}
