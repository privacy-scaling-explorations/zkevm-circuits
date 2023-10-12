use bus_mapping::{rpc::GethClient, state_db::StateDB};
use eth_types::{address, Address, Word, H256, U256};
use ethers_core::utils::rlp::Rlp;
use ethers_providers::Http;
use itertools::Itertools;
use std::{iter, str::FromStr};
use url::Url;
use zkevm_circuits::{
    mpt_circuit::witness_row::{Node2, StartNode},
    table::MPTProofType,
};

#[derive(Debug, Default, Clone)]
struct TrieModification {
    proof_type: MPTProofType,
    key: Word,
    value: Word,
    address: Address,
    nonce: u64,
    balance: U256,
    code_hash: H256,
}

fn generate_delete() {
    let keys = [
        Word::from("0xaaaabbbbabab"),
        Word::from("0xbaaabbbbabab"),
        Word::from("0xcaaabbbbabab"),
        Word::from("0xdaaabbbbabab"),
    ];

    // no zero. Hash
    let values = [1, 2, 3, 4];

    let addresses = iter::repeat(address!("0x50efbf12580138bc263c95757826df4e24eb81ff"))
        .take(4)
        .collect_vec();

    let to_be_modified = keys[3];
    let val = U256::zero(); // empty value deletes the key

    let trie_mod = TrieModification {
        proof_type: MPTProofType::StorageChanged,
        key: to_be_modified,
        value: val,
        address: addresses[0],
        ..Default::default()
    };

    // prepare state db
    // The go code fetched all accounts and proofs, why?
    let state_db = StateDB::new();

    let nodes = prepare_witness(vec![trie_mod], state_db);
    println!("nodes {}", serde_json::to_string_pretty(&nodes).unwrap());
    // dump nodes to file
}

struct AccountProof(Vec<String>);

fn prefetch_account(block_number: u64, address: Address) -> AccountProof {
    AccountProof(vec![])
}

fn prepare_witness(trie_modifications: Vec<TrieModification>, statedb: StateDB) -> Vec<Node2> {
    // mpt-witness-generator/witness/prepare_witness.go
    let mut nodes = vec![];
    for trie_mod in trie_modifications.iter() {
        match trie_mod.proof_type {
            MPTProofType::StorageChanged | MPTProofType::StorageDoesNotExist => {
                let s_root = H256::zero();
                let c_root = H256::zero();

                let nodes_account = convert_proof_to_witness();
                let nodes_storage = convert_proof_to_witness();

                nodes.push(start_node(trie_mod.proof_type, s_root, c_root));
                nodes.extend(nodes_account);
                nodes.extend(nodes_storage);
                nodes.push(end_node());
            }
            _ => {
                nodes = obtain_account_proof_and_convert_to_witness();
                return nodes;
            }
        }
    }
    nodes
}

fn obtain_account_proof_and_convert_to_witness() -> Vec<Node2> {
    vec![]
}

async fn get_account_proof() {
    let GETH0_URL = "http://localhost:8545/";
    let transport = Http::new(Url::parse(&GETH0_URL).expect("invalid url"));
    let client = GethClient::new(transport);
    let account = Address::from_str("0xccc9f924222776534d9bec025ef6231d8ae4d11a").unwrap();
    let keys = vec![Word::zero()];
    let block_num = 0;
    let proof = client
        .get_proof(account, keys, block_num.into())
        .await
        .unwrap();
    println!("proof {:?}", proof);
}

fn prepare_account_leaf_node() -> Node2 {
    // mpt-witness-generator/witness/leaf.go
    Node2::Account {
        node: todo!(),
        values: todo!(),
        keccak_data: todo!(),
    }
}

fn prepare_storage_leaf_node() -> Node2 {
    // mpt-witness-generator/witness/leaf.go
    Node2::Storage {
        node: todo!(),
        values: todo!(),
        keccak_data: todo!(),
    }
}

fn prepare_branch_node() -> Node2 {
    // mpt-witness-generator/witness/branch.go
    Node2::ExtensionBranch {
        node: todo!(),
        values: todo!(),
        keccak_data: todo!(),
    }
}

fn prepare_extensions() {
    // Return numberOfNibbles, listRlpBytes, values
}

fn add_branch_and_placeholder() -> Node2 {
    // mpt-witness-generator/witness/branch.go
    Node2::ExtensionBranch {
        node: todo!(),
        values: todo!(),
        keccak_data: todo!(),
    }
}

fn convert_proof_to_witness() -> Vec<Node2> {
    // 1. Determine upto
    // loop through upto
    //   if leaf
    //      prepare leaf
    //   else
    //      prepare branch
    // if lens not equal
    //  if additionalBranch
    //      addBranchAndPlaceholder
    //      prepare leaf and place holder
    //      prepareModExtensionNode
    //  else
    //      prepareLeafAndPlaceholderNode
    // else
    //  addBranchAndPlaceholder
    vec![]
}

fn start_node(proof_type: MPTProofType, s_root: H256, c_root: H256) -> Node2 {
    Node2::Start {
        // disable_preimage_check: oracle.PreventHashingInSecureTrie || specialTest == 5
        node: StartNode {
            disable_preimage_check: false,
            proof_type,
        },
        values: vec![
            iter::once(160)
                .chain(s_root.to_fixed_bytes())
                .chain(iter::once(0))
                .collect_vec()
                .into(),
            iter::once(160)
                .chain(c_root.to_fixed_bytes())
                .chain(iter::once(0))
                .collect_vec()
                .into(),
        ],
    }
}

fn end_node() -> Node2 {
    Node2::Start {
        node: StartNode {
            disable_preimage_check: false,
            proof_type: MPTProofType::Disabled,
        },
        values: vec![
            iter::once(160)
                .chain(iter::repeat(0))
                .take(32)
                .collect_vec()
                .into(),
            iter::once(160)
                .chain(iter::repeat(0))
                .take(32)
                .collect_vec()
                .into(),
        ],
    }
}
#[tokio::main]
async fn main() {
    println!("mpt testing case gen");
    // generate_delete()
    get_account_proof().await
}
