use bus_mapping::state_db::StateDB;
use eth_types::{address, Address, Word, H256, U256};
use ethers_core::types::Res;
use itertools::Itertools;
use std::{default, iter};
use zkevm_circuits::mpt_circuit::witness_row::Node;

#[derive(Clone, Default, Debug)]
enum ProofType {
    #[default]
    Disabled,
    NonceChanged,
    BalanceChanged,
    CodeHashChanged,
    AccountDestructed,
    AccountDoesNotExist,
    StorageChanged,
    StorageDoesNotExist,
    AccountCreate,
}

#[derive(Debug, Default, Clone)]
struct TrieModification {
    proof_type: ProofType,
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
        proof_type: ProofType::StorageChanged,
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

fn prefetch_account(block_number: u64, address: Address) -> AccountProof {}

fn prepare_witness(
    test_name: String,
    trie_modifications: Vec<TrieModification>,
    statedb: StateDB,
) -> Vec<Node> {
    // mpt-witness-generator/witness/prepare_witness.go
    for trie_mod in trie_modifications.iter() {
        match trie_mod.proof_type {
            ProofType::StorageChanged | ProofType::StorageDoesNotExist => {
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
                let mut nodes = vec![];
                // nodes.push(start_node)
                 // nodes.push(nodes_account)
                  // nodes.push(nodes_storage)
                  // nodes.push(end_node)
            }
            _ => {
                //   nodes = obtainAccountProofAndConvertToWitness(i, tMod, len(trieModifications),
                // statedb, specialTest)
            }
        }
    }
}
fn start_end_node(){


// func GetStartNode(proofType string, sRoot, cRoot common.Hash, specialTest byte) Node {
// 	s := StartNode{
// 		DisablePreimageCheck: oracle.PreventHashingInSecureTrie || specialTest == 5,
// 		ProofType:            proofType,
// 	}
// 	var values [][]byte
// 	var values1 []byte
// 	var values2 []byte
// 	values1 = append(values1, 160)
// 	values1 = append(values1, sRoot.Bytes()...)
// 	values1 = append(values1, 0)
// 	values2 = append(values2, 160)
// 	values2 = append(values2, cRoot.Bytes()...)
// 	values2 = append(values2, 0)

// 	values = append(values, values1)
// 	values = append(values, values2)

// 	return Node{
// 		Start:  &s,
// 		Values: values,
// 	}
// }

// func GetEndNode() Node {
// 	e := StartNode{
// 		DisablePreimageCheck: false,
// 		ProofType:            "Disabled",
// 	}

// 	endValues1, endValues2 := make([]byte, valueLen), make([]byte, valueLen)
// 	endValues1[0], endValues2[0] = 160, 160
// 	endValues := [][]byte{endValues1, endValues2}

// 	return Node{
// 		Start:  &e,
// 		Values: endValues,
// 	}
// }

}
fn main() {
    println!("mpt witness gen")
}
