package witness

import (
	"math/big"

	"main/gethutil/mpt/oracle"
	"main/gethutil/mpt/state"
	"main/gethutil/mpt/trie"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

const valueLen = 34
const modifiedExtensionNodeRowLen = 6

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

func obtainAccountProofAndConvertToWitness(tMod TrieModification, statedb *state.StateDB, specialTest byte) []Node {
	statedb.IntermediateRoot(false)

	addr := tMod.Address
	addrh := crypto.Keccak256(addr.Bytes())
	if oracle.AccountPreventHashingInSecureTrie {
		addrh = addr.Bytes()
		addrh = append(addrh, []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}...)
	}
	accountAddr := trie.KeybytesToHex(addrh)

	// This needs to be called before oracle.PrefetchAccount, otherwise oracle.PrefetchAccount
	// will cache the proof and won't return it.
	// Calling oracle.PrefetchAccount after statedb.SetStateObjectIfExists is needed only
	// for cases when statedb.loadRemoteAccountsIntoStateObjects = false.
	statedb.SetStateObjectIfExists(tMod.Address)

	oracle.PrefetchAccount(statedb.Db.BlockNumber, addr, nil)
	accountProof, aNeighbourNode1, aExtNibbles1, isLastLeaf1, aIsNeighbourNodeHashed1, err := statedb.GetProof(addr)
	check(err)

	var nodes []Node

	sRoot := statedb.GetTrie().Hash()

	if tMod.Type == NonceChanged {
		statedb.SetNonce(addr, tMod.Nonce)
	} else if tMod.Type == BalanceChanged {
		statedb.SetBalance(addr, tMod.Balance)
	} else if tMod.Type == CodeHashChanged {
		statedb.SetCodeHash(addr, tMod.CodeHash)
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
	aIsNeighbourNodeHashed := aIsNeighbourNodeHashed2
	if len(accountProof) > len(accountProof1) {
		// delete operation
		aNode = aNeighbourNode1
		isShorterProofLastLeaf = isLastLeaf2
		aIsNeighbourNodeHashed = aIsNeighbourNodeHashed1
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
		proofType = "CodeHashChanged"
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
			if oracle.AccountPreventHashingInSecureTrie {
				addrh = addr.Bytes()
				addrh = append(addrh, []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}...)
			}
			accountAddr := trie.KeybytesToHex(addrh)

			oracle.PrefetchAccount(statedb.Db.BlockNumber, addr, nil)
			oracle.PrefetchStorage(statedb.Db.BlockNumber, addr, tMod.Key, nil)

			if specialTest == 1 {
				statedb.CreateAccount(addr)
			}

			accountProof, aNeighbourNode1, aExtNibbles1, aIsLastLeaf1, aIsNeighbourNodeHashed1, err := statedb.GetProof(addr)
			check(err)

			// When the account has not been created yet and PrefetchAccount gets the wrong
			// account - because the first part of the address is the same and
			// the queried address doesn't have the account yet.
			if !statedb.Exist(addr) {
				// Note: the storage modification should not be the first modification for the account that does
				// not exist yet.
				panic("The account should exist at this point - created by SetNonce, SetBalance, or SetCodehash")
			}

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
			aIsNeighbourNodeHashed := aIsNeighbourNodeHashed2
			if len(accountProof) > len(accountProof1) {
				// delete operation
				aNode = aNeighbourNode1
				aIsLastLeaf = aIsLastLeaf2
				aIsNeighbourNodeHashed = aIsNeighbourNodeHashed1
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
			isNeighbourNodeHashed := isNeighbourNodeHashed2
			if len(storageProof) > len(storageProof1) {
				// delete operation
				node = neighbourNode1
				isLastLeaf = isLastLeaf2
				isNeighbourNodeHashed = isNeighbourNodeHashed1
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
			accountNodes := obtainAccountProofAndConvertToWitness(tMod, statedb, specialTest)
			nodes = append(nodes, accountNodes...)
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
	var extListRlpBytes []byte
	var extValues [][]byte
	for i := 0; i < 4; i++ {
		extValues = append(extValues, make([]byte, valueLen))
	}

	var nodes []Node

	for i := 0; i < upTo; i++ {
		if !isBranch(proof1[i]) {
			isNonExistingProof := (isAccountProof && nonExistingAccountProof) || (!isAccountProof && nonExistingStorageProof)
			areThereNibbles := len(extNibblesS[i]) != 0 || len(extNibblesC[i]) != 0
			// If i < upTo-1, it means it's not a leaf, so it's an extension node.
			// There is no any special relation between isNonExistingProof and isExtension,
			// except that in the non-existing proof the extension node can appear in `i == upTo-1`.
			// For non-existing proof, the last node in the proof could be an extension node (we have
			// nil in the underlying branch). For the non-existing proof with the wrong leaf
			// (non-existing proofs can be with a nil leaf or with a wrong leaf),
			// we don't need to worry because it appears in i = upTo-1).
			if (i != upTo-1) || (areThereNibbles && isNonExistingProof) { // extension node
				var numberOfNibbles byte
				isExtension = true
				numberOfNibbles, extListRlpBytes, extValues = prepareExtensions(extNibblesS[i], proof1[i], proof2[i])

				keyIndex += int(numberOfNibbles)
				continue
			}

			l := len(proof1)
			var node Node
			if isAccountProof {
				node = prepareAccountLeafNode(addr, addrh, proof1[l-1], proof2[l-1], nil, nil, key, false, false, false)
			} else {
				node = prepareStorageLeafNode(proof1[l-1], proof2[l-1], nil, nil, storage_key, key, nonExistingStorageProof, false, false, false, false)
			}

			nodes = append(nodes, node)
		} else {
			var extNode1 []byte = nil
			var extNode2 []byte = nil
			if isExtension {
				extNode1 = proof1[i-1]
				extNode2 = proof2[i-1]
			}

			bNode := prepareBranchNode(proof1[i], proof2[i], extNode1, extNode2, extListRlpBytes, extValues,
				key[keyIndex], key[keyIndex], false, false, isExtension, false)
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

			isModifiedExtNode, _, numberOfNibbles, bNode := addBranchAndPlaceholder(proof1, proof2,
				extNibblesS[len1-1], extNibblesC[len2-1],
				leafRow0, key,
				keyIndex, isShorterProofLastLeaf)

			nodes = append(nodes, bNode)

			var leafNode Node
			if isAccountProof {
				// Add account leaf after branch placeholder:
				if !isModifiedExtNode {
					leafNode = prepareAccountLeafNode(addr, addrh, proof1[len1-1], proof2[len2-1], nil, neighbourNode, key, false, false, false)
				} else {
					isSModExtension := false
					isCModExtension := false
					if len2 > len1 {
						isSModExtension = true
					} else {
						isCModExtension = true
					}
					leafNode = prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, isAccountProof, isSModExtension, isCModExtension)
				}
			} else {
				// Add storage leaf after branch placeholder
				if !isModifiedExtNode {
					leafNode = prepareStorageLeafNode(proof1[len1-1], proof2[len2-1], nil, neighbourNode, storage_key, key, nonExistingStorageProof, false, false, false, false)
				} else {
					isSModExtension := false
					isCModExtension := false
					if len2 > len1 {
						isSModExtension = true
					} else {
						isCModExtension = true
					}
					leafNode = prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, isAccountProof, isSModExtension, isCModExtension)
				}
			}

			// When a proof element is a modified extension node (new extension node appears at the position
			// of the existing extension node), additional rows are added (extension node before and after
			// modification).
			if isModifiedExtNode {
				leafNode = equipLeafWithModExtensionNode(statedb, leafNode, addr, proof1, proof2, extNibblesS, extNibblesC, key,
					keyIndex, numberOfNibbles, isAccountProof)
			}
			nodes = append(nodes, leafNode)
		} else {
			node := prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, isAccountProof, false, false)
			nodes = append(nodes, node)
		}
	} else {
		// Account proof has drifted leaf as the last row, storage proof has non-existing-storage row
		// as the last row.
		// When non existing proof and only the branches are returned, we add a placeholder leaf.
		// This is to enable the lookup (in account leaf row), most constraints are disabled for these rows.

		isLastBranch := isBranch(proof2[len(proof2)-1])

		if (len1 == 0 && len2 == 0) || isLastBranch {
			// We need to add a placeholder leaf
			if isAccountProof {
				node := prepareAccountLeafPlaceholderNode(addr, addrh, key, keyIndex)
				nodes = append(nodes, node)
			} else {
				node := prepareStorageLeafPlaceholderNode(storage_key, key, keyIndex)
				nodes = append(nodes, node)
			}
		} else {
			isLastExtNode := len(extNibblesC[len(proof2)-1]) != 0
			if isLastExtNode {
				// We need to add a placeholder branch and a placeholder leaf.
				// We are in a non-existing-proof and an extension node is the last element of getProof.
				// However, this extension node has not been added to the nodes yet (it's always added
				// together with a branch).
				
				nibbles := getNibbles(proof2[len(proof2)-1])
				newKey := make([]byte, len(key))
				copy(newKey, key)

				addr_nibbles := trie.KeybytesToHex(addrh)
				if isAccountProof {
					newKey = make([]byte, len(addr_nibbles))
					copy(newKey, addr_nibbles)
				}
				
				start := keyIndex - len(nibbles)

				nibblesMiddle := newKey[start:keyIndex]
				keyMiddle := []byte{160}
				keyMiddle = append(keyMiddle, trie.HexToCompact(nibblesMiddle)...)

				nibblesAfter := newKey[keyIndex:len(newKey)-1] // Remove the last flag (16)
				keyAfter := []byte{160}
				keyAfter = append(keyAfter, trie.HexToCompact(nibblesAfter)...)

				isExtension := true
				// Dummy branch. The constraint of the branch being in the extension node and the constraint of the
				// leaf being in the branch need to be disabled for this case.
				branchRlp := []byte{248, 81, 160, 244, 245, 0, 27, 233, 28, 128, 158, 163, 228, 185, 193, 250, 228, 226, 205, 233, 119, 98, 15, 183, 171, 187, 182, 172, 113, 115, 190, 167, 217, 33, 211, 160, 72, 229, 31, 123, 46, 26, 63, 24, 242, 142, 183, 252, 47, 111, 99, 255, 0, 118, 149, 196, 125, 165, 118, 4, 189, 149, 202, 221, 129, 141, 240, 209, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128};

				extNode := proof2[len(proof2)-1] // Let's name it E1
				bNode := prepareBranchNode(branchRlp, branchRlp, extNode, extNode, extListRlpBytes, extValues,
					key[keyIndex], key[keyIndex], false, false, isExtension, true)
				nodes = append(nodes, bNode)

				// Let's construct the leaf L1 that will have the correct key (the queried one)
				if isAccountProof {
					dummyLeaf := []byte{248,108,157,52,45,53,199,120,18,165,14,109,22,4,141,198,233,128,219,44,247,218,241,231,2,206,125,246,58,246,15,3,184,76,248,74,4,134,85,156,208,108,8,0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,112}
					node := prepareAccountLeafNode(addr, addrh, dummyLeaf, dummyLeaf, dummyLeaf, nil, addr_nibbles, false, false, false)

					node = equipLeafWithWrongExtension(node, keyMiddle, keyAfter, nibblesMiddle, nibblesAfter)

					nodes = append(nodes, node)
				} else {

					// The remaining `key` nibbles are to be stored in the constructed leaf - in our example [1 2 4 ...]
					compact := trie.HexToCompact(key[start:])
					// Add RLP:
					compactLen := byte(len(compact))
					rlp2 := 128 + compactLen
					rlp1 := 192 + compactLen + 1
					// Constructed leaf L1:
					dummyLeaf := append([]byte{rlp1, rlp2}, compact...)

					// Add dummy value:
					dummyLeaf = append(dummyLeaf, 0)

					node := prepareStorageLeafNode(dummyLeaf, dummyLeaf, dummyLeaf, nil, storage_key, key, nonExistingStorageProof, false, false, false, false)
					nodes = append(nodes, node)
				}
			}
		}
	}

	return nodes
}
