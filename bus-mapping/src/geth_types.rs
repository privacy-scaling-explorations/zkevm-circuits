//! Types needed for generating Ethereum traces

pub mod block;
pub mod call;
pub mod step;
pub mod tx;

pub use block::ZkEvmBlock;
pub use call::ZkEvmCall;
pub use step::ZkEvmExecStep;
pub use tx::ZkEvmTransaction;
