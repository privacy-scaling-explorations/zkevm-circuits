//! Module which contains all the RPC calls that are needed at any point to
//! query a Geth node in order to get a Block, Tx or Trace info.

use crate::eth_types::{
    Address, Block, GethExecTrace, Hash, ResultGethExecTraces, Transaction, U64,
};
use crate::Error;
use ethers_core::types::Bytes;
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
        contract_address: Address,
    ) -> Result<Vec<u8>, Error> {
        let address = serialize(&contract_address);
        let id = serialize(&"0x2".to_string());
        let code: Bytes = self
            .0
            .request("eth_getCode", [address, id])
            .await
            .map_err(|e| Error::JSONRpcError(e.into()))
            .unwrap();
        Ok(code.to_vec())
    }
}

#[cfg(test)]
mod rpc_tests {
    use super::*;
    use crate::evm::ProgramCounter;
    use ethers_providers::Http;
    use url::Url;

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
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
    #[ignore]
    #[tokio::test]
    async fn test_get_block_by_hash() {
        let prov = get_provider();
        let block_by_num_latest =
            prov.get_block_by_number(BlockNumber::Latest).await.unwrap();
        let block_by_hash = prov
            .get_block_by_hash(block_by_num_latest.hash.unwrap())
            .await
            .unwrap();
        assert!(block_by_hash.hash == block_by_hash.hash);
    }

    #[ignore]
    #[tokio::test]
    async fn test_get_contract_code() {
        let prov = get_provider();
        let contract_address =
            address!("0xd5f110b3e81de87f22fa8c5e668a5fc541c54e3d");
        let contract_code = Bytes::from(get_contract_vec_u8());
        let gotten_contract_code =
            prov.get_code_by_address(contract_address).await.unwrap();
        assert_eq!(contract_code.to_vec(), gotten_contract_code);
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
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
        assert_eq!(trace_by_hash[0].struct_logs.len(), 38);
        assert_eq!(
            trace_by_hash[0].struct_logs.last().unwrap().pc,
            ProgramCounter::from(94)
        );
    }

    // The test is ignored as the values used depend on the Geth instance used
    // each time you run the tests. And we can't assume that everyone will
    // have a Geth client synced with mainnet to have unified "test-vectors".
    #[ignore]
    #[tokio::test]
    async fn test_trace_block_by_number() {
        let prov = get_provider();
        let trace_by_hash = prov.trace_block_by_number(2.into()).await.unwrap();
        // Since we called in the test block the same transaction twice the len
        // should be the same and != 0.
        assert!(!trace_by_hash[0].struct_logs.is_empty());
        assert_eq!(trace_by_hash[0].struct_logs.len(), 38);
        assert_eq!(
            trace_by_hash[0].struct_logs.last().unwrap().pc,
            ProgramCounter::from(94)
        );
    }

    fn get_provider() -> GethClient<Http> {
        let transport = Http::new(Url::parse("http://localhost:8545").unwrap());
        GethClient::new(transport)
    }

    fn get_contract_vec_u8() -> Vec<u8> {
        vec![
            96, 128, 96, 64, 82, 52, 128, 21, 97, 0, 16, 87, 96, 0, 128, 253,
            91, 80, 96, 4, 54, 16, 97, 0, 65, 87, 96, 0, 53, 96, 224, 28, 128,
            99, 68, 93, 240, 172, 20, 97, 0, 70, 87, 128, 99, 141, 165, 203,
            91, 20, 97, 0, 100, 87, 128, 99, 253, 172, 213, 118, 20, 97, 0,
            174, 87, 91, 96, 0, 128, 253, 91, 97, 0, 78, 97, 0, 220, 86, 91,
            96, 64, 81, 128, 130, 129, 82, 96, 32, 1, 145, 80, 80, 96, 64, 81,
            128, 145, 3, 144, 243, 91, 97, 0, 108, 97, 0, 226, 86, 91, 96, 64,
            81, 128, 130, 115, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 22, 115,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 22, 129, 82, 96, 32, 1, 145, 80,
            80, 96, 64, 81, 128, 145, 3, 144, 243, 91, 97, 0, 218, 96, 4, 128,
            54, 3, 96, 32, 129, 16, 21, 97, 0, 196, 87, 96, 0, 128, 253, 91,
            129, 1, 144, 128, 128, 53, 144, 96, 32, 1, 144, 146, 145, 144, 80,
            80, 80, 97, 1, 7, 86, 91, 0, 91, 96, 1, 84, 129, 86, 91, 96, 0,
            128, 144, 84, 144, 97, 1, 0, 10, 144, 4, 115, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 22, 129, 86, 91, 96, 0, 128, 144, 84, 144, 97, 1, 0,
            10, 144, 4, 115, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 22, 115, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 22, 51, 115, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 22, 20, 97, 1, 172, 87, 96, 64, 81, 127, 8, 195, 121,
            160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 129, 82, 96, 4, 1, 128, 128, 96, 32, 1, 130,
            129, 3, 130, 82, 96, 51, 129, 82, 96, 32, 1, 128, 97, 1, 183, 96,
            51, 145, 57, 96, 64, 1, 145, 80, 80, 96, 64, 81, 128, 145, 3, 144,
            253, 91, 128, 96, 1, 129, 144, 85, 80, 80, 86, 254, 84, 104, 105,
            115, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 115, 32,
            114, 101, 115, 116, 114, 105, 99, 116, 101, 100, 32, 116, 111, 32,
            116, 104, 101, 32, 99, 111, 110, 116, 114, 97, 99, 116, 39, 115,
            32, 111, 119, 110, 101, 114, 162, 101, 98, 122, 122, 114, 49, 88,
            32, 7, 48, 47, 32, 138, 16, 104, 103, 105, 80, 155, 82, 158, 24,
            120, 189, 161, 133, 152, 131, 119, 141, 112, 222, 221, 24, 68, 254,
            121, 12, 155, 222, 100, 115, 111, 108, 99, 67, 0, 5, 16, 0, 50,
        ]
    }
}
