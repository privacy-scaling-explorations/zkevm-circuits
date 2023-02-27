//! This mod used by public input circuit

use crate::error::Error;
use crate::rpc::GethClient;
use eth_types::{Bytes, H256};
use ethers_core::abi::{Function, Param, ParamType, StateMutability, Token};
use ethers_providers::JsonRpcClient;

use lazy_static::lazy_static;

lazy_static! {
    static ref PROPOSE_TX: Function = Function {
        name: "proposeBlock".to_string(),
        inputs: vec![Param {
            name: "inputs".to_string(),
            kind: ParamType::Array(Box::new(ParamType::Bytes)),
            internal_type: None,
        },],
        outputs: vec![],
        #[allow(deprecated)]
        constant: Some(false),
        state_mutability: StateMutability::NonPayable,
    };
}

/// Get the l2 transaction list data from l1's propose transaction's calldata
pub async fn get_txs_rlp<P: JsonRpcClient>(
    l1_cli: &GethClient<P>,
    propose_tx_hash: H256,
) -> Result<Bytes, Error> {
    let tx = l1_cli.get_transaction_by_hash(propose_tx_hash).await?;
    // remove 4bytes short signature
    // signature+inputs
    if tx.input.len() < 4 {
        return Err(Error::InternalError(
            "parse propose input: unexpected input length",
        ));
    }

    let mut result = PROPOSE_TX
        .decode_input(&tx.input[4..])
        .map_err(|_| Error::InternalError("parse propose input: failed"))?;
    if result.len() != 1 {
        return Err(Error::InternalError(
            "parse propose input: unexpected params count",
        ));
    }
    Ok(match result.swap_remove(0) {
        Token::Array(mut inputs) => {
            if inputs.len() != 2 {
                return Err(Error::InternalError(
                    "parse propose input: unexpected inputs length",
                ));
            }
            match inputs.swap_remove(1) {
                Token::Bytes(rlp) => rlp.into(),
                _ => {
                    return Err(Error::InternalError(
                        "parse propose input: unexpected inputs[1] type",
                    ));
                }
            }
        }
        _ => {
            return Err(Error::InternalError(
                "parse propose input: unexpected inputs type",
            ));
        }
    })
}
