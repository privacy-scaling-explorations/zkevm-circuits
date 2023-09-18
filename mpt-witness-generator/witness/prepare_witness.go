package witness

import (
	"fmt"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/oracle"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/state"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/trie"
)

const branchNodeRLPLen = 2 // we have two positions for RLP meta data
const branch2start = branchNodeRLPLen + 32
const branchRows = 19 // 1 (init) + 16 (children) + 2 (extension S and C)

// rowLen - each branch node has 2 positions for RLP meta data and 32 positions for hash
const rowLen = branch2start + 2 + 32 + 1 // +1 is for info about what type of row is it
const valueLen = 34
const driftedPos = 13
const isExtensionPos = 14

// extension key even or odd is about nibbles - that determines whether the first byte (not
// considering RLP bytes) is 0 or 1 (see encoding.go hexToCompact)
const isExtShortC16Pos = 21
const isExtShortC1Pos = 22
const isExtLongEvenC16Pos = 23
const isExtLongEvenC1Pos = 24
const isExtLongOddC16Pos = 25
const isExtLongOddC1Pos = 26

// short/long means having one or more than one nibbles
const isSExtLongerThan55Pos = 27
const isExtNodeSNonHashedPos = 31

// nibbles_counter_pos = 33, set in the assign function.
const isShortExtNodeBranch = 36

type AccountRowType int64

const (
	AccountKeyS AccountRowType = iota
	AccountKeyC
	AccountNonceS
	AccountBalanceS
	AccountStorageS
	AccountCodehashS
	AccountNonceC
	AccountBalanceC
	AccountStorageC
	AccountCodehashC
	AccountDrifted
	AccountWrong
)

type ProofType int64

const (
	Disabled ProofType = iota
	NonceChanged
	BalanceChanged
	CodeHashChanged
	AccountDestructed
	AccountDoesNotExist
	StorageChanged
	StorageDoesNotExist
	AccountCreate
)

type TrieModification struct {
	Type     ProofType
	Key      common.Hash
	Value    common.Hash
	Address  common.Address
	Nonce    uint64
	Balance  *big.Int
	CodeHash []byte
}

// GetWitness is to be used by external programs to generate the witness.
func GetWitness(nodeUrl string, blockNum int, trieModifications []TrieModification) []Node {
	blockNumberParent := big.NewInt(int64(blockNum))
	oracle.NodeUrl = nodeUrl
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	return obtainTwoProofsAndConvertToWitness(trieModifications, statedb, 0)
}

func obtainAccountProofAndConvertToWitness(i int, tMod TrieModification, tModsLen int, statedb *state.StateDB, specialTest byte) []Node {
	statedb.IntermediateRoot(false)

	addr := tMod.Address
	addrh := crypto.Keccak256(addr.Bytes())
	accountAddr := trie.KeybytesToHex(addrh)

	// This needs to called before oracle.PrefetchAccount, otherwise oracle.PrefetchAccount
	// will cache the proof and won't return it.
	// Calling oracle.PrefetchAccount after statedb.SetStateObjectIfExists is needed only
	// for cases when statedb.loadRemoteAccountsIntoStateObjects = false.
	statedb.SetStateObjectIfExists(tMod.Address)

	oracle.PrefetchAccount(statedb.Db.BlockNumber, tMod.Address, nil)
	accountProof, aNeighbourNode1, aExtNibbles1, isLastLeaf1, aIsNeighbourNodeHashed1, err := statedb.GetProof(addr)
	check(err)

	var nodes []Node

	sRoot := statedb.GetTrie().Hash()

	if tMod.Type == NonceChanged {
		statedb.SetNonce(addr, tMod.Nonce)
	} else if tMod.Type == BalanceChanged {
		statedb.SetBalance(addr, tMod.Balance)
	} else if tMod.Type == CodeHashChanged {
		statedb.SetCode(addr, tMod.CodeHash)
	} else if tMod.Type == AccountCreate {
		statedb.CreateAccount(tMod.Address)
	} else if tMod.Type == AccountDestructed {
		statedb.DeleteAccount(tMod.Address)
	}
	// No statedb change in case of AccountDoesNotExist.

	statedb.IntermediateRoot(false)

	cRoot := statedb.GetTrie().Hash()

	accountProof1, aNeighbourNode2, aExtNibbles2, isLastLeaf2, aIsNeighbourNodeHashed2, err := statedb.GetProof(addr)
	check(err)

	if tMod.Type == AccountDoesNotExist && len(accountProof) == 0 {
		// If there is only one account in the state trie and we want to prove for some
		// other account that it doesn't exist.
		// We get the root node (the only account) and put it as the only element of the proof,
		// it will act as a "wrong" leaf.
		account, err := statedb.GetTrieRootElement()
		check(err)
		accountProof = make([][]byte, 1)
		accountProof[0] = account
		accountProof1 = make([][]byte, 1)
		accountProof1[0] = account
	}

	addrh, accountAddr, accountProof, accountProof1, sRoot, cRoot = modifyAccountProofSpecialTests(addrh, accountAddr, sRoot, cRoot, accountProof, accountProof1, aNeighbourNode2, specialTest)
	aNode := aNeighbourNode2
	isShorterProofLastLeaf := isLastLeaf1
	aIsNeighbourNodeHashed := aIsNeighbourNodeHashed1
	if len(accountProof) > len(accountProof1) {
		// delete operation
		aNode = aNeighbourNode1
		isShorterProofLastLeaf = isLastLeaf2
		aIsNeighbourNodeHashed = aIsNeighbourNodeHashed2
	}

	if aIsNeighbourNodeHashed {
		aNode, _ = oracle.Preimage(common.BytesToHash(aNode[1:]))
	}

	proofType := "NonceChanged"
	if tMod.Type == BalanceChanged {
		proofType = "BalanceChanged"
	} else if tMod.Type == AccountDestructed {
		proofType = "AccountDestructed"
	} else if tMod.Type == AccountDoesNotExist {
		proofType = "AccountDoesNotExist"
	} else if tMod.Type == CodeHashChanged {
		proofType = "CodeHashExists" // TODO: change when it changes in the circuit
	}

	nodes = append(nodes, GetStartNode(proofType, sRoot, cRoot, specialTest))

	nodesAccount :=
		convertProofToWitness(statedb, addr, addrh, accountProof, accountProof1, aExtNibbles1, aExtNibbles2, tMod.Key, accountAddr, aNode, true, tMod.Type == AccountDoesNotExist, false, isShorterProofLastLeaf)
	nodes = append(nodes, nodesAccount...)
	nodes = append(nodes, GetEndNode())

	return nodes
}

// obtainTwoProofsAndConvertToWitness obtains the GetProof proof before and after the modification for each
// of the modification. It then converts the two proofs into an MPT circuit witness. Witness is thus
// prepared for each of the modifications and the witnesses are chained together - the final root of
// the previous witness is the same as the start root of the current witness.
func obtainTwoProofsAndConvertToWitness(trieModifications []TrieModification, statedb *state.StateDB, specialTest byte) []Node {
	statedb.IntermediateRoot(false)
	var nodes []Node

	for i := 0; i < len(trieModifications); i++ {
		tMod := trieModifications[i]
		if tMod.Type == StorageChanged || tMod.Type == StorageDoesNotExist {
			kh := crypto.Keccak256(tMod.Key.Bytes())
			if oracle.PreventHashingInSecureTrie {
				kh = tMod.Key.Bytes()
			}
			keyHashed := trie.KeybytesToHex(kh)

			addr := tMod.Address
			addrh := crypto.Keccak256(addr.Bytes())
			accountAddr := trie.KeybytesToHex(addrh)

			oracle.PrefetchAccount(statedb.Db.BlockNumber, tMod.Address, nil)
			oracle.PrefetchStorage(statedb.Db.BlockNumber, addr, tMod.Key, nil)

			if specialTest == 1 {
				statedb.CreateAccount(addr)
			}

			accountProof, aNeighbourNode1, aExtNibbles1, aIsLastLeaf1, aIsNeighbourNodeHashed1, err := statedb.GetProof(addr)
			check(err)
			storageProof, neighbourNode1, extNibbles1, isLastLeaf1, isNeighbourNodeHashed1, err := statedb.GetStorageProof(addr, tMod.Key)
			check(err)

			sRoot := statedb.GetTrie().Hash()

			if tMod.Type == StorageChanged {
				statedb.SetState(addr, tMod.Key, tMod.Value)
				statedb.IntermediateRoot(false)
			}

			cRoot := statedb.GetTrie().Hash()

			proofType := "StorageChanged"
			if tMod.Type == StorageDoesNotExist {
				proofType = "StorageDoesNotExist"
			}

			accountProof1, aNeighbourNode2, aExtNibbles2, aIsLastLeaf2, aIsNeighbourNodeHashed2, err := statedb.GetProof(addr)
			check(err)

			storageProof1, neighbourNode2, extNibbles2, isLastLeaf2, isNeighbourNodeHashed2, err := statedb.GetStorageProof(addr, tMod.Key)
			check(err)

			aNode := aNeighbourNode2
			aIsLastLeaf := aIsLastLeaf1
			aIsNeighbourNodeHashed := aIsNeighbourNodeHashed1
			if len(accountProof) > len(accountProof1) {
				// delete operation
				aNode = aNeighbourNode1
				aIsLastLeaf = aIsLastLeaf2
				aIsNeighbourNodeHashed = aIsNeighbourNodeHashed2
			}

			// Note: oracle.Preimage is called here and not in Proof function because the preimage
			// is not available yet there (GetProof / GetStorageProof fetch the preimages).
			if aIsNeighbourNodeHashed {
				// The error is not handled here, because it is ok to continue when the preimage is not found
				// for the cases when neighbour node is not needed. 
				aNode, _ = oracle.Preimage(common.BytesToHash(aNode[1:]))
			}

			node := neighbourNode2
			isLastLeaf := isLastLeaf1
			isNeighbourNodeHashed := isNeighbourNodeHashed1
			if len(storageProof) > len(storageProof1) {
				// delete operation
				node = neighbourNode1
				isLastLeaf = isLastLeaf2
				isNeighbourNodeHashed = isNeighbourNodeHashed2
			}

			if isNeighbourNodeHashed {
				// The error is not handled here, because it is ok to continue when the preimage is not found
				// for the cases when neighbour node is not needed. 
				node, _ = oracle.Preimage(common.BytesToHash(node[1:]))
			}

			if specialTest == 1 {
				if len(accountProof1) != 2 {
					panic("account should be in the second level (one branch above it)")
				}
				accountProof, accountProof1, sRoot, cRoot = modifyAccountSpecialEmptyTrie(addrh, accountProof1[len(accountProof1)-1])
			}

			// Needs to be after `specialTest == 1` preparation:
			nodes = append(nodes, GetStartNode(proofType, sRoot, cRoot, specialTest))

			// In convertProofToWitness, we can't use account address in its original form (non-hashed), because
			// of the "special" test for which we manually manipulate the "hashed" address and we don't have a preimage.
			// TODO: addr is used for calling GetProof for modified extension node only, might be done in a different way
			nodesAccount :=
				convertProofToWitness(statedb, addr, addrh, accountProof, accountProof1, aExtNibbles1, aExtNibbles2, tMod.Key, accountAddr, aNode, true, tMod.Type == AccountDoesNotExist, false, aIsLastLeaf)
			nodes = append(nodes, nodesAccount...)
			nodesStorage :=
				convertProofToWitness(statedb, addr, addrh, storageProof, storageProof1, extNibbles1, extNibbles2, tMod.Key, keyHashed, node, false, false, tMod.Type == StorageDoesNotExist, isLastLeaf)
			nodes = append(nodes, nodesStorage...)
			nodes = append(nodes, GetEndNode())
		} else {
			nodes = obtainAccountProofAndConvertToWitness(i, tMod, len(trieModifications), statedb, specialTest)
		}
	}

	return nodes
}

// prepareWitness obtains the GetProof proof before and after the modification for each
// of the modification. It then converts the two proofs into an MPT circuit witness for each of
// the modifications and stores it into a file.
func prepareWitness(testName string, trieModifications []TrieModification, statedb *state.StateDB) {
	nodes := obtainTwoProofsAndConvertToWitness(trieModifications, statedb, 0)
	StoreNodes(testName, nodes)
}

// prepareWitnessSpecial obtains the GetProof proof before and after the modification for each
// of the modification. It then converts the two proofs into an MPT circuit witness for each of
// the modifications and stores it into a file. It is named special as the flag specialTest
// instructs the function obtainTwoProofsAndConvertToWitness to prepare special trie states, like moving
// the account leaf in the first trie level.
func prepareWitnessSpecial(testName string, trieModifications []TrieModification, statedb *state.StateDB, specialTest byte) {
	nodes := obtainTwoProofsAndConvertToWitness(trieModifications, statedb, specialTest)
	StoreNodes(testName, nodes)
}

// updateStateAndPrepareWitness updates the state according to the specified keys and values and then
// prepares a witness for the proof before given modifications and after.
// This function is used when some specific trie state needs to be prepared before the actual modifications
// take place and for which the witness is needed.
func updateStateAndPrepareWitness(testName string, keys, values []common.Hash, addresses []common.Address,
	trieModifications []TrieModification) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	statedb.DisableLoadingRemoteAccounts()

	// Set the state needed for the test:
	for i := 0; i < len(keys); i++ {
		statedb.SetState(addresses[i], keys[i], values[i])
	}

	prepareWitness(testName, trieModifications, statedb)
}

// convertProofToWitness takes two GetProof proofs (before and after a single modification) and prepares
// a witness for the MPT circuit. Alongside, it prepares the byte streams that need to be hashed
// and inserted into the Keccak lookup table.
func convertProofToWitness(statedb *state.StateDB, addr common.Address, addrh []byte, proof1, proof2, extNibblesS, extNibblesC [][]byte, storage_key common.Hash, key []byte, neighbourNode []byte,
	isAccountProof, nonExistingAccountProof, nonExistingStorageProof, isShorterProofLastLeaf bool) []Node {
	rows := make([][]byte, 0)
	toBeHashed := make([][]byte, 0)

	minLen := len(proof1)
	if len(proof2) < minLen {
		minLen = len(proof2)
	}

	keyIndex := 0
	len1 := len(proof1)
	len2 := len(proof2)

	// When a value in the trie is updated, both proofs are of the same length.
	// Otherwise, when a value is added (not updated) and there is no node which needs to be changed
	// into a branch, one proof has a leaf and one does not have it.
	// The third option is when a value is added and the existing leaf is turned into a branch,
	// in this case we have an additional branch in C proof (when deleting a value causes
	// that a branch with two leaves turns into a leaf, we have an additional branch in S proof).

	additionalBranch := false
	if len1 < len2 && len1 > 0 { // len = 0 when trie trie is empty
		// Check if the last proof element in the shorter proof is a leaf -
		// if it is, then there is an additional branch.
		additionalBranch = !isBranch(proof1[len1-1])
	} else if len2 < len1 && len2 > 0 {
		additionalBranch = !isBranch(proof2[len2-1])
	}

	upTo := minLen
	if (len1 != len2) && additionalBranch {
		upTo = minLen - 1
	}

	var isExtension bool
	extensionNodeInd := 0

	var extListRlpBytes []byte
	var extValues [][]byte
	for i := 0; i < 4; i++ {
		extValues = append(extValues, make([]byte, valueLen))
	}

	var nodes []Node

	branchC16 := byte(0)
	branchC1 := byte(1)
	for i := 0; i < upTo; i++ {
		if !isBranch(proof1[i]) {
			if i != len1-1 { // extension node
				var numberOfNibbles byte
				isExtension = true
				numberOfNibbles, extListRlpBytes, extValues = prepareExtensions(extNibblesS, extensionNodeInd, proof1[i], proof2[i])

				keyIndex += int(numberOfNibbles)
				extensionNodeInd++
				continue
			}

			l := len(proof1)
			var node Node
			if isAccountProof {
				node = prepareAccountLeafNode(addr, addrh, proof1[l-1], proof2[l-1], nil, key, false, false, false)
			} else {
				node = prepareStorageLeafNode(proof1[l-1], proof2[l-1], nil, storage_key, key, nonExistingStorageProof, false, false, false, false)
			}

			nodes = append(nodes, node)
		} else {
			switchC16 := true // If not extension node, switchC16 = true.
			if isExtension {
				keyLen := getExtensionNodeKeyLen(proof1[i-1])
				if keyLen == 1 {
					switchC16 = false
				} else {
					if proof1[i-1][2] != 0 { // If even, switch16 = true.
						switchC16 = false
					}
				}
			}
			if switchC16 {
				if branchC16 == 1 {
					branchC16 = 0
					branchC1 = 1
				} else {
					branchC16 = 1
					branchC1 = 0
				}
			}

			var extNode1 []byte = nil
			var extNode2 []byte = nil
			if isExtension {
				extNode1 = proof1[i-1]
				extNode2 = proof2[i-1]
			}

			bNode := prepareBranchNode(proof1[i], proof2[i], extNode1, extNode2, extListRlpBytes, extValues,
				key[keyIndex], key[keyIndex], branchC16, branchC1, false, false, isExtension, false, false)
			nodes = append(nodes, bNode)

			keyIndex += 1

			isExtension = false
		}
	}

	if len1 != len2 {
		if additionalBranch {
			leafRow0 := proof1[len1-1] // To compute the drifted position.
			if len1 > len2 {
				leafRow0 = proof2[len2-1]
			}

			isModifiedExtNode, _, numberOfNibbles, branchC16, bNode := addBranchAndPlaceholder(proof1, proof2, extNibblesS, extNibblesC,
				leafRow0, key, neighbourNode,
				keyIndex, extensionNodeInd, additionalBranch,
				isAccountProof, nonExistingAccountProof, isShorterProofLastLeaf, branchC16, branchC1, &toBeHashed)

			nodes = append(nodes, bNode)

			if isAccountProof {
				// Add account leaf after branch placeholder:
				var node Node
				if !isModifiedExtNode {
					node = prepareAccountLeafNode(addr, addrh, proof1[len1-1], proof2[len2-1], neighbourNode, key, false, false, false)
				} else {
					isSModExtension := false
					isCModExtension := false
					if len2 > len1 {
						isSModExtension = true
					} else {
						isCModExtension = true
					}
					node = prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, nonExistingAccountProof, isAccountProof, isSModExtension, isCModExtension)
				}
				nodes = append(nodes, node)
			} else {
				// Add storage leaf after branch placeholder
				var node Node
				if !isModifiedExtNode {
					node = prepareStorageLeafNode(proof1[len1-1], proof2[len2-1], neighbourNode, storage_key, key, nonExistingStorageProof, false, false, false, false)
				} else {
					isSModExtension := false
					isCModExtension := false
					if len2 > len1 {
						isSModExtension = true
					} else {
						isCModExtension = true
					}
					node = prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, nonExistingAccountProof, isAccountProof, isSModExtension, isCModExtension)
				}
				nodes = append(nodes, node)
			}

			// When a proof element is a modified extension node (new extension node appears at the position
			// of the existing extension node), additional rows are added (extension node before and after
			// modification).
			if isModifiedExtNode {
				// TODO
				modExtensionNode := prepareModExtensionNode(statedb, addr, &rows, proof1, proof2, extNibblesS, extNibblesC, key, neighbourNode,
					keyIndex, extensionNodeInd, numberOfNibbles, additionalBranch,
					isAccountProof, nonExistingAccountProof, isShorterProofLastLeaf, branchC16, branchC1, &toBeHashed)
				// node = append(nodes, modExtensionNode)
				fmt.Println(modExtensionNode)
			}
		} else {
			node := prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, nonExistingAccountProof, isAccountProof, false, false)
			nodes = append(nodes, node)
		}
	} else if isBranch(proof2[len(proof2)-1]) {
		// Account proof has drifted leaf as the last row, storage proof has non-existing-storage row
		// as the last row.
		// When non existing proof and only the branches are returned, we add a placeholder leaf.
		// This is to enable the lookup (in account leaf row), most constraints are disabled for these rows.

		if isAccountProof {
			node := prepareAccountLeafPlaceholderNode(addr, addrh, key, keyIndex)
			nodes = append(nodes, node)
		} else {
			node := prepareStorageLeafPlaceholderNode(storage_key, key, keyIndex)
			nodes = append(nodes, node)
		}
	}

	return nodes
}
