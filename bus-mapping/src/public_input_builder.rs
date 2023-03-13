//! This mod used by public input circuit

use crate::error::Error;
use crate::rpc::GethClient;
use eth_types::{Bytes, H256};
use ethers_core::abi::{Function, Param, ParamType, StateMutability, Token};
use ethers_providers::JsonRpcClient;

use lazy_static::lazy_static;

lazy_static! {
    static ref PROPOSE_TX: Function = {
        #[allow(deprecated)]
        Function {
            name: "proposeBlock".to_string(),
            inputs: vec![Param {
                name: "inputs".to_string(),
                kind: ParamType::Array(Box::new(ParamType::Bytes)),
                internal_type: None,
            }],
            outputs: vec![],
            constant: Some(false),
            state_mutability: StateMutability::NonPayable,
        }
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

#[cfg(test)]
mod tests {
    use ethers_core::utils::rlp;
    use ethers_providers::Http;
    use std::str::FromStr;

    use super::*;
    #[tokio::test]
    async fn test() {
        let l1_provider =
            Http::from_str("https://l1rpc.internal.taiko.xyz").expect("Http geth url");
        let l1_geth_client = GethClient::new(l1_provider);
        let propose_tx_hash = H256::from_slice(
            &hex::decode("14a59537d5de49c0ef010bb94228237f32b5994d42954e61e5a4c84f6f991298")
                .unwrap(),
        );
        let tx = get_txs_rlp(&l1_geth_client, propose_tx_hash).await.unwrap();
        let txs: Vec<eth_types::Transaction> = rlp::Rlp::new(&tx).as_list().unwrap();
        println!("{:?}", txs);
    }
}
