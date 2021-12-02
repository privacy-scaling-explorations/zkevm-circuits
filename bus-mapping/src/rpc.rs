//! Module which contains all the RPC calls that are needed at any point to
//! query a Geth node in order to get a Block, Tx or Trace info.

use crate::eth_types::{
    Address, Block, EIP1186ProofResponse, GethExecTrace, Hash,
    ResultGethExecTraces, Transaction, Word, U64,
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

    /// Calls `eth_getProof` via JSON-RPC returning a [`EIP1186ProofResponse`]
    /// returning the account and storage-values of the specified
    /// account including the Merkle-proof.
    pub async fn get_proof(
        &self,
        account: Address,
        keys: Vec<Word>,
        block_num: BlockNumber,
    ) -> Result<EIP1186ProofResponse, Error> {
        let account = serialize(&account);
        let keys = serialize(&keys);
        let num = block_num.serialize();
        self.0
            .request("eth_getProof", [account, keys, num])
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

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_get_proof() {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());
        let prov = GethClient::new(transport);

        let address =
            Address::from_str("0x7F0d15C7FAae65896648C8273B6d7E43f58Fa842")
                .unwrap();
        let keys = vec![Word::from_str("0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").unwrap()];
        let proof = prov
            .get_proof(address, keys, BlockNumber::Latest)
            .await
            .unwrap();
        const TARGET_PROOF: &str = r#"{
            "address": "0x7f0d15c7faae65896648c8273b6d7e43f58fa842",
            "accountProof": [
                "0xf873a12050fb4d3174ec89ef969c09fd4391602169760fb005ad516f5d172cbffb80e955b84ff84d8089056bc75e2d63100000a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
            ],
            "balance": "0x0",
            "codeHash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            "nonce": "0x0",
            "storageHash": "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
            "storageProof": [
                {
                    "key": "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
                    "value": "0x0",
                    "proof": []
                }
            ]
        }"#;
        assert!(
            serde_json::from_str::<EIP1186ProofResponse>(TARGET_PROOF).unwrap()
                == proof
        );
    }
}
