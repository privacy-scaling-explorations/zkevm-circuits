package witness

import (
	"fmt"
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
	TransactionInsertion
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

	// This needs to be called before oracle.PrefetchAccount, otherwise oracle.PrefetchAccount
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
		statedb.SetCodeHash(addr, tMod.CodeHash)
	} else if tMod.Type == AccountCreate {
		statedb.CreateAccount(tMod.Address)
	} else if tMod.Type == AccountDestructed {
		statedb.DeleteAccount(tMod.Address)
	}
	// No statedb change in case of AccountDoesNotExist and TransactionInsertion

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
			accountAddr := trie.KeybytesToHex(addrh)

			oracle.PrefetchAccount(statedb.Db.BlockNumber, tMod.Address, nil)
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
			accountNodes := obtainAccountProofAndConvertToWitness(i, tMod, len(trieModifications), statedb, specialTest)
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

// For stack trie, we have the following combinations ([proofS] -> [proofC])
//
// --- special case for the first 2 txs
// A. [(empty)] -> [LEAF] --> 1
// B. [LEAF] -> [EXT - BRANCH - LEAF] --> 2
//
// --- most of cases
// C. [(EXT, BRANCH)] -> [(EXT, BRANCH) - LEAF]
//
// --- both proofs end with a leaf node
// D. [BRANCH - LEAF] -> [BRANCH - BRANCH - LEAF]  --> 129
// E. [(EXT, BRANCH) - LEAF] -> [(EXT, BRANCH) - EXT - BRANCH - LEAF] --> 130, 514
//
// --- TODO: modified extension nodes, not working now
// M1. [EXT - BRANCH] -> [BRANCH - LEAF]  --> 0 under 16 txs or 16 (modified ext.)
// M2. [(BRANCH) - EXT - BRANCH - HASHED] -> [(BRANCH) - BRANCH - LEAF] --> 144
// M3. [(BRANCH, EXT) - BRANCH - HASHED] -> [(BRANCH, EXT) - LEAF] -->  512
// Issue:
// Take tx144 as example, the proof is
// [BRANCH_S1 - BRANCH_S2 - EXT_S - BRANCH_S3 - HASHED] -> [BRANCH_C1 - BRANCH_C2 - BRANCH_C3 - LEAF]
// We need to generate a json with nodes
// [{BRANCH_S1-BRANCH_C1}, {BRANCH_S2-BRANCH_C2}, {EXT_S, BRANCH_S3-placeholder}, {placeholder-BRANCH_C3}, {placeholder-LEAF}]
// We didn't have the 4th node, {placeholder-BRANCH_C3} now.
func GenerateWitness(txIdx uint, key, value []byte, proof *trie.StackProof) []Node {
	k := trie.KeybytesToHex(key)
	k = k[:len(k)-1]
	// padding k to 32 bytes
	kk := make([]byte, 32-len(k))
	k = append(k, kk...)
	fmt.Println("== txIdx", txIdx)
	// fmt.Println(" k", k)

	proofS := proof.GetProofS()
	proofC := proof.GetProofC()
	extNibblesS := proof.GetNibblesS()
	extNibblesC := proof.GetNibblesC()
	proofTypeS := proof.GetTypeS()
	proofTypeC := proof.GetTypeC()

	len1 := len(proofS)
	len2 := len(proofC)
	var nodes []Node

	// Special case for the 1st tx, an empty stack trie
	if len1 == 0 {
		leafNode := prepareTxLeafAndPlaceholderNode(1, proofC[0], k, false)
		return append(nodes, leafNode)
	}

	keyIndex := 0
	minLen := min(len1, len2)
	lastProofTypeS := proofTypeS[len1-1]
	lastProofTypeC := proofTypeC[len2-1]

	upTo := minLen
	additionalBranch := true

	// If both of proofs end with either a leaf or a hashed node, e.g. [BRANCH - LEAF] --> [BRANCH - BRANCH - LEAF]
	// The 2nd BRANCH in above proofC should have a branch placeholder for it.
	// We handle branch placeholder in `additionalBranch` and that's why we need to minus `upTo` by 1 here.
	if len1 != len2 &&
		(lastProofTypeS == trie.LeafNode || lastProofTypeS == trie.HashedNode) &&
		(lastProofTypeC == trie.LeafNode || lastProofTypeC == trie.HashedNode) {
		upTo--
	}

	// The length of proofS and proofC is equal and the last element of proofS is a hashed node or a leaf
	if len1 == len2 && (lastProofTypeS == trie.LeafNode || lastProofTypeS == trie.HashedNode) {
		additionalBranch = false
	}

	// Special case for the 2nd tx.
	// In this case, proofS only contains a leaf node and proofC is [EXT - BRANCH - LEAF].
	// `additionalBranch` can handle the mismatched the order of the type.
	if len1 == 1 && lastProofTypeS == trie.LeafNode {
		upTo = 0
	}

	var extListRlpBytes []byte
	var extValues [][]byte
	for i := 0; i < 4; i++ {
		extValues = append(extValues, make([]byte, 34))
	}

	var numberOfNibbles byte
	isExtension := false
	mismatchedIdx := -1
	fmt.Println("upto", upTo, additionalBranch, proofTypeS)
	for i := 0; i < upTo; i++ {
		if proofTypeS[i] != trie.BranchNode {
			// This is for the case of extension modified node due to the order of the types mismatched.
			// See this example,
			// [BRANCH - BRANCH - EXT - BRANCH - HASHED] -> [BRANCH - BRANCH - BRANCH - LEAF]
			// In this case, `mismatchedIdx`` is 2 and stops at `EXT` node
			if proofTypeS[i] != proofTypeC[i] {
				mismatchedIdx = i
				break
			}

			areThereNibbles := len(extNibblesS[i]) != 0 || len(extNibblesC[i]) != 0
			if areThereNibbles { // extension node
				isExtension = true
				numberOfNibbles, extListRlpBytes, extValues = prepareExtensions(extNibblesS[i], proofS[i], proofC[i])
				keyIndex += int(numberOfNibbles)
				continue
			}

			node := prepareTxLeafNode(txIdx, proofS[len1-1], proofC[len2-1], k, nil, false, false, false)
			nodes = append(nodes, node)
		} else {
			var extNode1 []byte = nil
			var extNode2 []byte = nil
			if isExtension {
				extNode1 = proofS[i-1]
				extNode2 = proofC[i-1]
			}

			bNode := prepareBranchNode(
				proofS[i], proofC[i], extNode1, extNode2, extListRlpBytes,
				extValues, k[keyIndex], k[keyIndex],
				false, false, isExtension)

			nodes = append(nodes, bNode)
			keyIndex += 1
			isExtension = false
		}
	}

	// To address the length of proofS and proofC is not equal or the order of the type is matched.
	if additionalBranch {
		lastProofType := lastProofTypeS
		leafRow0 := proofS[len1-1] // To compute the drifted position.
		if len1 > len2 {
			leafRow0 = proofC[len2-1]
			lastProofType = lastProofTypeC
		}

		// In most of cases, proofs are like this [BRANCH - (BRANCH, EXT)] -> [BRANCH - (BRANCH, EXT) - LEAF]
		// That means proofC only appends a leaf node to proofS.
		// In such cases, we don't need to add a placeholder branch
		need_branch_placeholder :=
			!(len1 == len2-1 && (lastProofTypeS != lastProofTypeC) && (lastProofTypeC == trie.LeafNode))
		if need_branch_placeholder {
			var extProofS []byte
			if mismatchedIdx != -1 {
				extProofS = proofS[mismatchedIdx]
			}

			// This is a special case when the number of txs is 2.
			// In this case, proofS is a leaf and len1 is 1, but there is no nibbles
			var lastExtNibbleS []byte
			if len(extNibblesS) != 0 {
				lastExtNibbleS = extNibblesS[len1-1]
			}

			var branchNode Node
			_, _, _, branchNode = addBranchAndPlaceholder(
				proofS, proofC, lastExtNibbleS, extNibblesC[len2-1], extProofS,
				leafRow0, k, keyIndex, lastProofType == 3)
			nodes = append(nodes, branchNode)
		}

		var leafNode Node
		// In stack trie proofs, the order of the type is the same except the case of modification extension node
		// So, we use `mismatchedIdx` to represent the case.
		if mismatchedIdx == -1 {
			// Add a tx leaf after branch placeholder
			if lastProofTypeS == trie.LeafNode {
				leafNode = prepareTxLeafNode(txIdx, proofS[len1-1], proofC[len2-1], k, nil, isBranch(proofS[len1-1]), false, false)
			} else {
				leafNode = prepareTxLeafAndPlaceholderNode(txIdx, proofC[len2-1], k, false)
			}

		} else {
			fmt.Println("MODIFIED EXT CASE!!")
			leafNode = prepareTxLeafAndPlaceholderNode(txIdx, proofC[len2-1], k, true)

			// When a proof element is a modified extension node (new extension node appears at the position
			// of the existing extension node), additional rows are added (extension node before and after
			// modification).
			leafNode = equipLeafWithModExtensionNode(nil, leafNode, common.Address{byte(txIdx)}, proofS, proofC,
				extNibblesS, extNibblesC, proofS[mismatchedIdx], k, keyIndex, int(numberOfNibbles), false)
		}
		nodes = append(nodes, leafNode)
	}

	return nodes
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
func convertProofToWitness(
	statedb *state.StateDB, addr common.Address, addrh []byte,
	proof1, proof2, extNibblesS, extNibblesC [][]byte,
	storage_key common.Hash, key []byte, neighbourNode []byte,
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
	extensionNodeInd := 0

	var extListRlpBytes []byte
	var extValues [][]byte
	for i := 0; i < 4; i++ {
		extValues = append(extValues, make([]byte, valueLen))
	}

	var nodes []Node

	for i := 0; i < upTo; i++ {
		if !isBranch(proof1[i]) {
			isNonExistingProof := (isAccountProof && nonExistingAccountProof) || (!isAccountProof && nonExistingStorageProof)
			var curExtNibblesS, curExtNibblesC []byte
			if len(extNibblesS) > i {
				curExtNibblesS = extNibblesS[i]
			}
			if len(extNibblesC) > i {
				curExtNibblesC = extNibblesC[i]
			}
			areThereNibbles := len(curExtNibblesS) != 0 || len(curExtNibblesC) != 0
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
				numberOfNibbles, extListRlpBytes, extValues = prepareExtensions(curExtNibblesS, proof1[i], proof2[i])

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
			var extNode1 []byte = nil
			var extNode2 []byte = nil
			if isExtension {
				extNode1 = proof1[i-1]
				extNode2 = proof2[i-1]
			}

			bNode := prepareBranchNode(proof1[i], proof2[i], extNode1, extNode2, extListRlpBytes, extValues,
				key[keyIndex], key[keyIndex], false, false, isExtension)
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

			var lastExtNibbleS, lastExtNibbleC []byte
			if len(extNibblesS) != 0 {
				lastExtNibbleS = extNibblesS[len(extNibblesS)-1]
			}
			if len(extNibblesC) != 0 {
				lastExtNibbleC = extNibblesC[len(extNibblesC)-1]
			}

			isModifiedExtNode, _, numberOfNibbles, bNode :=
				addBranchAndPlaceholder(proof1, proof2, lastExtNibbleS, lastExtNibbleC, nil, leafRow0, key, keyIndex, isShorterProofLastLeaf)

			nodes = append(nodes, bNode)

			var leafNode Node
			if isAccountProof {
				// Add account leaf after branch placeholder:
				if !isModifiedExtNode {
					leafNode = prepareAccountLeafNode(addr, addrh, proof1[len1-1], proof2[len2-1], neighbourNode, key, false, false, false)
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
					leafNode = prepareStorageLeafNode(proof1[len1-1], proof2[len2-1], neighbourNode, storage_key, key, nonExistingStorageProof, false, false, false, false)
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
				leafNode = equipLeafWithModExtensionNode(statedb, leafNode, addr, proof1, proof2, extNibblesS, extNibblesC, nil,
					key, keyIndex, numberOfNibbles, isAccountProof)
			}
			nodes = append(nodes, leafNode)
		} else {
			node := prepareLeafAndPlaceholderNode(addr, addrh, proof1, proof2, storage_key, key, isAccountProof, false, false)
			nodes = append(nodes, node)
		}
	} else if (len1 == 0 && len2 == 0) || isBranch(proof2[len(proof2)-1]) {
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
