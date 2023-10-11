use bus_mapping::state_db::StateDB;
use eth_types::{address, Address, Word, H256, U256};
use itertools::Itertools;
use std::iter;
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
    let state_db;

    // func prepareWitness(testName string, trieModifications []TrieModification, statedb
    // *state.StateDB) {     nodes := obtainTwoProofsAndConvertToWitness(trieModifications,
    // statedb, 0)     StoreNodes(testName, nodes)
    // }
}

struct AccountProof(Vec<String>);

fn prefetch_account(block_number: u64, address: Address) -> AccountProof {
    AccountProof(vec![])
}

fn prepare_witness(
    test_name: String,
    trie_modifications: Vec<TrieModification>,
    statedb: StateDB,
) -> Vec<Node2> {
    // mpt-witness-generator/witness/prepare_witness.go
    let mut nodes = vec![];
    for trie_mod in trie_modifications.iter() {
        match trie_mod.proof_type {
            MPTProofType::StorageChanged | MPTProofType::StorageDoesNotExist => {
                //     kh := crypto.Keccak256(tMod.Key.Bytes())
                //     if oracle.PreventHashingInSecureTrie {
                //         kh = tMod.Key.Bytes()
                //     }
                //     keyHashed := trie.KeybytesToHex(kh)

                //     addr := tMod.Address
                //     addrh := crypto.Keccak256(addr.Bytes())
                //     accountAddr := trie.KeybytesToHex(addrh)

                //     oracle.PrefetchAccount(statedb.Db.BlockNumber, tMod.Address, nil)
                //     // oracle.PrefetchStorage(statedb.Db.BlockNumber, addr, tMod.Key, nil)

                //     if specialTest == 1 {
                //         statedb.CreateAccount(addr)
                //     }

                //     accountProof, aNeighbourNode1, aExtNibbles1, aIsLastLeaf1, err :=
                // statedb.GetProof(addr)     check(err)
                //     storageProof, neighbourNode1, extNibbles1, isLastLeaf1, err :=
                // statedb.GetStorageProof(addr, tMod.Key)     check(err)

                //     sRoot := statedb.GetTrie().Hash()

                //     if tMod.Type == StorageChanged {
                //         statedb.SetState(addr, tMod.Key, tMod.Value)
                //         statedb.IntermediateRoot(false)
                //     }

                //     cRoot := statedb.GetTrie().Hash()

                //     proofType := "StorageChanged"
                //     if tMod.Type == StorageDoesNotExist {
                //         proofType = "StorageDoesNotExist"
                //     }

                //     accountProof1, aNeighbourNode2, aExtNibbles2, aIsLastLeaf2, err :=
                // statedb.GetProof(addr)     check(err)

                //     storageProof1, neighbourNode2, extNibbles2, isLastLeaf2, err :=
                // statedb.GetStorageProof(addr, tMod.Key)     check(err)

                //     aNode := aNeighbourNode2
                //     aIsLastLeaf := aIsLastLeaf1
                //     if len(accountProof) > len(accountProof1) {
                //         // delete operation
                //         aNode = aNeighbourNode1
                //         aIsLastLeaf = aIsLastLeaf2
                //     }

                //     node := neighbourNode2
                //     isLastLeaf := isLastLeaf1
                //     if len(storageProof) > len(storageProof1) {
                //         // delete operation
                //         node = neighbourNode1
                //         isLastLeaf = isLastLeaf2
                //     }

                //     if specialTest == 1 {
                //         if len(accountProof1) != 2 {
                //             panic("account should be in the second level (one branch above it)")
                //         }
                //         accountProof, accountProof1, sRoot, cRoot =
                // modifyAccountSpecialEmptyTrie(addrh, accountProof1[len(accountProof1)-1])
                //     }

                // },

                nodes.push(start_node(trie_mod.proof_type, s_root, c_root));
                // nodes.push(nodes_account)
                // nodes.push(nodes_storage)
                nodes.push(end_node());
            }
            _ => {
                //   nodes = obtainAccountProofAndConvertToWitness(i, tMod, len(trieModifications),
                // statedb, specialTest)
            }
        }
    }
    nodes
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
fn main() {
    println!("mpt witness gen")
}
