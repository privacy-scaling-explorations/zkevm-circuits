//! re-export external crate ethers
pub use ethers::{
    contract::{builders::ContractCall, Contract, ContractFactory},
    middleware::SignerMiddleware,
    solc::Solc,
};
