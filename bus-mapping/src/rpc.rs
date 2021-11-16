//! Module which contains all the RPC calls that are needed at any point to query a Geth node in order to get a Block, Tx or Trace info.

use crate::eth_types::{Block, Hash, Transaction};
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

/// Placeholder structure designed to contain the methods that the BusMapping needs in order to enable Geth queries.
pub struct GethClient<P: JsonRpcClient>(P);

impl<P: JsonRpcClient> GethClient<P> {
    /// Generates a new `GethClient` instance.
    pub fn new(provider: P) -> Self {
        Self(provider)
    }

    /// Calls `eth_getBlockByHash` via JSON-RPC returning a [`Block`] returning only the list of tx_hashes involved on it.
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
}

#[cfg(test)]
mod rpc_tests {
    use super::*;
    use ethers_providers::Http;
    use std::str::FromStr;
    use url::Url;

    // The test is ignored as the values used depend on the Geth instance used each time you run the tests.
    // And we can't assume that everyone will have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_get_block_by_hash() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());

        let hash = Hash::from_str("0x60d58d0e417b2b7fab8c74a5efc8292cb5651cd056caad126fb308523b40abc2").unwrap();
        let prov = GethClient::new(transport);
        let block = prov.get_block_by_hash(hash).await.unwrap();
        assert!(hash == block.transactions[0].hash)
    }
}
