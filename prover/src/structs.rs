#[derive(Debug, Clone, serde::Serialize)]
pub struct Proofs {
    pub state_proof: eth_types::Bytes,
    pub evm_proof: eth_types::Bytes,
}

#[derive(Debug, serde::Serialize)]
pub struct JsonRpcError {
    pub code: i32,
    pub message: String,
}

#[derive(Debug, serde::Serialize)]
pub struct JsonRpcResponseError {
    pub jsonrpc: String,
    pub id: serde_json::Value,
    pub error: JsonRpcError,
}

#[derive(Debug, serde::Serialize)]
pub struct JsonRpcResponse<T: serde::Serialize> {
    pub jsonrpc: String,
    pub id: serde_json::Value,
    pub result: T,
}

#[derive(Debug, serde::Deserialize)]
pub struct JsonRpcRequest<T: serde::Serialize> {
    pub id: serde_json::Value,
    pub method: String,
    pub params: T,
}

#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct ProofRequestOptions {
    /// the block number
    pub block: u64,
    /// the rpc url
    pub rpc: String,
    /// retry proof computation if error
    pub retry: bool,
    /// parameter file to use
    pub param: String,
}

impl PartialEq for ProofRequestOptions {
    fn eq(&self, other: &Self) -> bool {
        self.block == other.block && self.rpc == other.rpc && self.param == other.param
    }
}
