//! Module which contains all the RPC calls that are needed at any point to
//! query a Geth node in order to get a Block, Tx or Trace info.

use crate::eth_types::{
    Address, Block, GethExecTrace, Hash, ResultGethExecTraces, Transaction,
    Word, H256, U256, U64,
};
use crate::Error;
use ethers_core::types::Bytes;
use ethers_providers::JsonRpcClient;
use serde::{Deserialize, Serialize};

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
#[derive(Debug, Deserialize, Serialize)]
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

/// Struct used to define the storage proof
#[derive(Debug, Default, Clone, PartialEq, Deserialize, Serialize)]
pub struct StorageProof {
    key: H256,
    proof: Vec<Bytes>,
    value: U256,
}

/// Struct used to define the result of `eth_getProof` call
#[derive(Debug, Default, Clone, PartialEq, Deserialize, Serialize)]
pub struct EIP1186ProofResponse {
    /// The balance of the account
    pub balance: U256,
    /// The hash of the code of the account
    pub codeHash: H256,
    /// The nonce of the account
    pub nonce: U256,
    /// SHA3 of the StorageRoot
    pub storageHash: H256,
    /// Array of rlp-serialized MerkleTree-Nodes
    pub accountProof: Vec<Bytes>,
    /// Array of storage-entries as requested
    pub storageProof: Vec<StorageProof>,
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
        contract_address: Address,
        block_num: BlockNumber,
    ) -> Result<Vec<u8>, Error> {
        let address = serialize(&contract_address);
        let num = block_num.serialize();
        let resp: Bytes = self
            .0
            .request("eth_getCode", [address, num])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))?;
        Ok(resp.to_vec())
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
        let num = block_num.serialize();
        self.0
            .request("eth_getProof", [account, keys, num])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))
    }
}

#[cfg(feature = "geth_rpc_test")]
#[cfg(test)]
mod rpc_tests {
    use super::*;
    use crate::evm::ProgramCounter;
    use ethers_providers::Http;
    use std::str::FromStr;
    use url::Url;

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[tokio::test]
    async fn test_get_block_by_number() {
        let prov = get_provider();
        let block_by_num_latest =
            prov.get_block_by_number(BlockNumber::Latest).await.unwrap();
        let block_by_num = prov.get_block_by_number(2u64.into()).await.unwrap();
        assert!(
            block_by_num.transactions[0].hash
                == block_by_num_latest.transactions[0].hash
        );
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[tokio::test]
    async fn test_get_block_by_hash() {
        let prov = get_provider();
        let block_by_num_latest =
            prov.get_block_by_number(BlockNumber::Latest).await.unwrap();
        let block_by_hash = prov
            .get_block_by_hash(block_by_num_latest.hash.unwrap())
            .await
            .unwrap();
        assert!(block_by_num_latest.hash == block_by_hash.hash);
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[tokio::test]
    async fn test_get_contract_code() {
        let prov = get_provider();
        let contract_address =
            address!("0xd5f110b3e81de87f22fa8c5e668a5fc541c54e3d");
        let contract_code = get_contract_vec_u8();
        let gotten_contract_code = prov
            .get_code_by_address(contract_address, BlockNumber::Latest)
            .await
            .unwrap();
        assert_eq!(contract_code, gotten_contract_code);
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[tokio::test]
    async fn test_trace_block_by_hash() {
        let prov = get_provider();
        let block_by_num_latest =
            prov.get_block_by_number(BlockNumber::Latest).await.unwrap();
        let block_by_hash = prov
            .get_block_by_hash(block_by_num_latest.hash.unwrap())
            .await
            .unwrap();
        let trace_by_hash = prov
            .trace_block_by_hash(block_by_hash.hash.unwrap())
            .await
            .unwrap();
        assert!(!trace_by_hash[0].struct_logs.is_empty());
        assert_eq!(trace_by_hash[0].struct_logs.len(), 116);
        assert_eq!(
            trace_by_hash[0].struct_logs.last().unwrap().pc,
            ProgramCounter::from(180)
        );
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[tokio::test]
    async fn test_trace_block_by_number() {
        let prov = get_provider();
        let trace_by_hash = prov
            .trace_block_by_number(BlockNumber::Latest)
            .await
            .unwrap();
        // Since we called in the test block the same transaction twice the len
        // should be the same and != 0.
        assert!(!trace_by_hash[0].struct_logs.is_empty());
        assert_eq!(trace_by_hash[0].struct_logs.len(), 116);
        assert_eq!(
            trace_by_hash[0].struct_logs.last().unwrap().pc,
            ProgramCounter::from(180)
        );
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
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
                "0xf9011180a0ab8cdb808c8303bb61fb48e276217be9770fa83ecf3f90f2234d558885f5abf18080a01a697e814758281972fcd13bc9707dbcd2f195986b05463d7b78426508445a04a01f5061d0eb56546aa17ec23486841e6cf073d98069c4b41c3fc9a0dc1cab0c89a0929ef457bb59f8a38d431af8d917ce82a8b608bd50edfc2b4a04f8b7bd7c583580a02e0d86c3befd177f574a20ac63804532889077e955320c9361cd10b7cc6f580980a064b03ddf9f38fbbf8d0cf12171626ed809fcc99d85e30fe6a2cca7a0ee7475178080a01b7779e149cadf24d4ffb77ca7e11314b8db7097e4d70b2a173493153ca2e5a0a066a7662811491b3d352e969506b420d269e8b51a224f574b3b38b3463f43f0098080",
                "0xf851a070ebfba8dc7e9dd75891224e8cce5b757c74f9879d7d4a2665e7e422aa0aed4480808080808080808080a0e61e567237b49c44d8f906ceea49027260b4010c10a547b38d8b131b9d3b6f848080808080"
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
        let target_proof =
            serde_json::from_str::<EIP1186ProofResponse>(TARGET_PROOF).unwrap();
        assert_eq!(proof.balance, target_proof.balance);
        assert_eq!(proof.codeHash, target_proof.codeHash);
        assert_eq!(proof.nonce, target_proof.nonce);
        assert_eq!(proof.storageHash, target_proof.storageHash);
        assert_eq!(proof.storageProof, target_proof.storageProof);
    }

    fn get_provider() -> GethClient<Http> {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());
        GethClient::new(transport)
    }

    fn get_contract_vec_u8() -> Vec<u8> {
        vec![
            96, 128, 96, 64, 82, 52, 128, 21, 97, 0, 16, 87, 96, 0, 128, 253,
            91, 80, 96, 4, 54, 16, 97, 0, 76, 87, 96, 0, 53, 96, 224, 28, 128,
            99, 33, 132, 140, 70, 20, 97, 0, 81, 87, 128, 99, 46, 100, 206,
            193, 20, 97, 0, 109, 87, 128, 99, 176, 242, 183, 42, 20, 97, 0,
            139, 87, 128, 99, 243, 65, 118, 115, 20, 97, 0, 167, 87, 91, 96, 0,
            128, 253, 91, 97, 0, 107, 96, 4, 128, 54, 3, 129, 1, 144, 97, 0,
            102, 145, 144, 97, 1, 60, 86, 91, 97, 0, 197, 86, 91, 0, 91, 97, 0,
            117, 97, 0, 218, 86, 91, 96, 64, 81, 97, 0, 130, 145, 144, 97, 1,
            120, 86, 91, 96, 64, 81, 128, 145, 3, 144, 243, 91, 97, 0, 165, 96,
            4, 128, 54, 3, 129, 1, 144, 97, 0, 160, 145, 144, 97, 1, 60, 86,
            91, 97, 0, 227, 86, 91, 0, 91, 97, 0, 175, 97, 0, 237, 86, 91, 96,
            64, 81, 97, 0, 188, 145, 144, 97, 1, 120, 86, 91, 96, 64, 81, 128,
            145, 3, 144, 243, 91, 128, 96, 0, 129, 144, 85, 80, 96, 0, 97, 0,
            215, 87, 96, 0, 128, 253, 91, 80, 86, 91, 96, 0, 128, 84, 144, 80,
            144, 86, 91, 128, 96, 0, 129, 144, 85, 80, 80, 86, 91, 96, 0, 128,
            97, 0, 249, 87, 96, 0, 128, 253, 91, 96, 0, 84, 144, 80, 144, 86,
            91, 96, 0, 128, 253, 91, 96, 0, 129, 144, 80, 145, 144, 80, 86, 91,
            97, 1, 25, 129, 97, 1, 6, 86, 91, 129, 20, 97, 1, 36, 87, 96, 0,
            128, 253, 91, 80, 86, 91, 96, 0, 129, 53, 144, 80, 97, 1, 54, 129,
            97, 1, 16, 86, 91, 146, 145, 80, 80, 86, 91, 96, 0, 96, 32, 130,
            132, 3, 18, 21, 97, 1, 82, 87, 97, 1, 81, 97, 1, 1, 86, 91, 91, 96,
            0, 97, 1, 96, 132, 130, 133, 1, 97, 1, 39, 86, 91, 145, 80, 80,
            146, 145, 80, 80, 86, 91, 97, 1, 114, 129, 97, 1, 6, 86, 91, 130,
            82, 80, 80, 86, 91, 96, 0, 96, 32, 130, 1, 144, 80, 97, 1, 141, 96,
            0, 131, 1, 132, 97, 1, 105, 86, 91, 146, 145, 80, 80, 86, 254, 162,
            100, 105, 112, 102, 115, 88, 34, 18, 32, 198, 65, 17, 183, 105,
            192, 24, 239, 185, 163, 114, 200, 208, 240, 163, 224, 232, 124,
            166, 82, 153, 136, 202, 171, 161, 44, 117, 159, 44, 234, 223, 52,
            100, 115, 111, 108, 99, 67, 0, 8, 10, 0, 51,
        ]
    }
}
