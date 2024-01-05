use std::collections::HashMap;

use ethers::utils::hex::FromHex;
use light_client_poc::verifier::{self, ProofType, TrieModification};
use revm::{
    db::{CacheDB, EmptyDB},
    primitives::{
        ruint::Uint, AccountInfo, Address, Bytecode, Bytes, CreateScheme, TransactTo, U256,
    },
    EVM,
};
use wasm_bindgen::prelude::*;

use crate::rpc::{get_block, get_code};
use eyre::{eyre, Result};

mod externs;
mod rpc;

// Pending stuff
// - At this moment we are not able to guarantee that the inital state in the proof contains all
//   entries requiered by the EVM. So the EVM should check if accounts used pre-exists in the db.
// - EVM does not process the coinbase

async fn exec_block(block_no: u64, initial_state: Vec<TrieModification>) -> Result<()> {
    // populate database

    let mut db = CacheDB::new(EmptyDB::default());
    let mut accounts = HashMap::<Address, AccountInfo>::new();

    for entry in initial_state {
        let address = Address::from_slice(entry.address.as_fixed_bytes());
        let mut account_info = accounts.entry(address).or_insert(AccountInfo::default());

        let mut value_bytes = [0u8; 32];
        entry.value.to_little_endian(&mut value_bytes);
        let value = U256::from_le_bytes(value_bytes);

        let slot = U256::from_le_bytes(*entry.key.as_fixed_bytes());

        let balance_changed: u8 = ProofType::BalanceChanged.into();
        let nonce_changed: u8 = ProofType::NonceChanged.into();
        let code_hash_changed: u8 = ProofType::CodeHashChanged.into();
        let storage_changed: u8 = ProofType::StorageChanged.into();

        if entry.typ as u8 == balance_changed {
            account_info.balance = value;
        } else if entry.typ as u8 == nonce_changed {
            account_info.nonce = value.into_limbs()[0];
        } else if entry.typ as u8 == code_hash_changed {
            let code = get_code(entry.address, block_no).await?;
            account_info.code_hash = value.into();
            account_info.code = Some(Bytecode::new_raw(code.into()));
        } else if entry.typ as u8 == storage_changed {
            db.insert_account_storage(address, slot, value)?;
        } else {
            return Err(eyre!("Unknown proof type: {}", entry.typ as u8));
        }
    }

    for (address, account_info) in accounts {
        db.insert_account_info(address, account_info);
    }

    let mut evm: EVM<CacheDB<EmptyDB>> = EVM::new();
    evm.database(db);

    // get block and execute transactions

    let block = get_block(block_no).await?;

    for tx in block.transactions {
        let from: Address = tx.from.parse()?;
        let to = if tx.to.is_empty() {
            TransactTo::Create(CreateScheme::Create)
        } else {
            TransactTo::Call(tx.to.parse()?)
        };

        // fill in missing bits of env struct
        // change that to whatever caller you want to be
        evm.env.tx.caller = from;
        // account you want to transact with
        evm.env.tx.transact_to = to;
        // calldata formed via abigen
        evm.env.tx.data = Bytes::from_hex(tx.input)?;
        // transaction value in wei
        evm.env.tx.value = match Uint::<256, 4>::from_str_radix(&tx.value, 16) {
            Ok(v) => v,
            Err(err) => return Err(eyre!("Error parsing tx value: {}", err)),
        };
        evm.env.tx.gas_limit = tx.gas.parse()?;
        evm.env.tx.gas_price = match Uint::<256, 4>::from_str_radix(&tx.gasPrice, 16) {
            Ok(v) => v,
            Err(err) => return Err(eyre!("Error parsing tx gas price: {}", err)),
        };
        let _result = evm.transact().unwrap();
    }

    Ok(())
}

#[wasm_bindgen]
pub async fn verify_proof() -> String {
    let block_no = 107;
    let fk = include_str!("../../block-107.fk");
    let proof = include_str!("../../block-107.proof");
    let data = include_str!("../../block-107.data");

    let verifier_data: verifier::InitialStateCircuitVerifierData =
        serde_json::from_str(data).unwrap();

    if let Err(err) = exec_block(block_no, verifier_data.trie_modifications).await {
        return format!("error:{}", err);
    }

    verifier::wasm_verify_serialized(data, fk, proof)
}
