package witness

import (
	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/state"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/trie"
)

// prepareModExtensionNode adds rows for a modified extension node before and after modification.
// These rows are added only when an existing extension node gets shortened or elongated (in terms
// of the extension node nibbles) because of another extension node being added or deleted.
// The rows added are somewhat exceptional as otherwise they do not appear.
func prepareModExtensionNode(statedb *state.StateDB, addr common.Address, rows *[][]byte, proof1, proof2,
	extNibblesS, extNibblesC [][]byte,
	key, neighbourNode []byte,
	keyIndex, extensionNodeInd, numberOfNibbles int,
	additionalBranch, isAccountProof, nonExistingAccountProof,
	isShorterProofLastLeaf bool, branchC16, branchC1 byte, toBeHashed *[][]byte) Node {
	len1 := len(proof1)
	len2 := len(proof2)

	var longExtNode []byte
	if len1 > len2 {
		longExtNode = proof2[len2-1]
	} else {
		longExtNode = proof1[len1-1]
	}

	var extNibbles [][]byte
	if len1 > len2 {
		extNibbles = extNibblesC
	} else {
		extNibbles = extNibblesS
	}

	numberOfNibbles0, extensionRowS, extensionRowC :=
		prepareExtensionRows(extNibbles, extensionNodeInd, longExtNode, longExtNode, true, false)

	extNodeSelectors := make([]byte, rowLen)
	setExtNodeSelectors(extNodeSelectors, longExtNode, int(numberOfNibbles0), branchC16)
	extNodeSelectors = append(extNodeSelectors, 24)

	_, extListRlpBytesS, extValuesS := prepareExtensions(extNibbles, extensionNodeInd, longExtNode, longExtNode)
	/*
		b := []byte{249, 1, 49, 128} // We don't really need a branch info (only extension node).
		longNode := prepareBranchNode(b, b, longExtNode, longExtNode, extListRlpBytes, extValues,
			key[keyIndex], key[keyIndex], branchC16, branchC1, false, false, true, false, false)
	*/

	var extRows [][]byte
	// We need to prove the old extension node is in S proof (when ext. node inserted).
	extRows = append(extRows, extNodeSelectors)
	extRows = append(extRows, extensionRowS)
	extRows = append(extRows, extensionRowC)

	*rows = append(*rows, extRows...)
	// addForHashing(longExtNode, toBeHashed)

	// Get nibbles of the extension node that gets shortened because of the newly insertd
	// extension node:
	longNibbles := getExtensionNodeNibbles(longExtNode)

	ind := byte(keyIndex) + byte(numberOfNibbles) // where the old and new extension nodes start to be different
	// diffNibble := oldNibbles[ind]
	longExtNodeKey := make([]byte, len(key))
	copy(longExtNodeKey, key)
	// We would like to retrieve the shortened extension node from the trie via GetProof or
	// GetStorageProof (depending whether it is an account proof or storage proof),
	// the key where we find its underlying branch is `oldExtNodeKey`.
	for j := ind; int(j) < keyIndex+len(longNibbles); j++ {
		// keyIndex is where the nibbles of the old and new extension node start
		longExtNodeKey[j] = longNibbles[j-byte(keyIndex)]
	}

	k := trie.HexToKeybytes(longExtNodeKey)
	ky := common.BytesToHash(k)
	var proof [][]byte
	var err error
	if isAccountProof {
		proof, _, _, _, err = statedb.GetProof(addr)
	} else {
		proof, _, _, _, err = statedb.GetStorageProof(addr, ky)
	}
	check(err)

	// There is no short extension node when `len(longNibbles) - numberOfNibbles = 1`, in this case there
	// is simply a branch instead.
	shortExtNodeIsBranch := len(longNibbles)-numberOfNibbles == 1
	if shortExtNodeIsBranch {
		(*rows)[len(*rows)-branchRows-9][isShortExtNodeBranch] = 1
	}

	var shortExtNode []byte
	/*
		extNodeSelectors1 := make([]byte, rowLen)
		emptyExtRows := prepareEmptyExtensionRows(false, true)
		extensionRowS1 := emptyExtRows[0]
		extensionRowC1 := emptyExtRows[1]
	*/

	var extListRlpBytesC []byte
	var extValuesC [][]byte

	if !shortExtNodeIsBranch {
		if len2 > len1 {
			isItBranch := isBranch(proof[len(proof)-1])

			// Note that `oldExtNodeKey` has nibbles properly set only up to the end of nibbles,
			// this is enough to get the old extension node by `GetProof` or `GetStorageProof` -
			// we will get its underlying branch, but sometimes also the leaf in a branch if
			// the nibble will correspond to the leaf (we left the nibbles from
			// `keyIndex + len(oldNibbles)` the same as the nibbles in the new extension node).

			if isItBranch { // last element in a proof is a branch
				shortExtNode = proof[len(proof)-2]
			} else { // last element in a proof is a leaf
				shortExtNode = proof[len(proof)-3]
			}
		} else {
			// Needed only for len1 > len2
			(*rows)[len(*rows)-branchRows-9][driftedPos] = longNibbles[numberOfNibbles]

			shortNibbles := longNibbles[numberOfNibbles+1:]
			compact := trie.HexToCompact(shortNibbles)
			longStartBranch := 2 + (longExtNode[1] - 128) // cannot be "short" in terms of having the length at position 0; TODO: extension with length at position 2 not supported (the probability very small)

			if len(shortNibbles) > 1 {
				// add RLP2:
				compact = append([]byte{128 + byte(len(compact))}, compact...)
			}

			shortExtNode = append(compact, longExtNode[longStartBranch:]...)

			// add RLP1:
			shortExtNode = append([]byte{192 + byte(len(shortExtNode))}, shortExtNode...)
		}

		// Get the nibbles of the shortened extension node:
		nibbles := getExtensionNodeNibbles(shortExtNode)

		// Enable `prepareExtensionRows` call:
		extNibbles = append(extNibbles, nibbles)

		/*
			var numberOfNibbles1 byte
			numberOfNibbles1, extensionRowS1, extensionRowC1 =
				prepareExtensionRows(extNibbles, extensionNodeInd + 1, shortExtNode, shortExtNode, false, true)
		*/

		_, extListRlpBytesC, extValuesC = prepareExtensions(extNibbles, extensionNodeInd+1, shortExtNode, shortExtNode)
		/*
			shortNode = prepareBranchNode(b, b, shortExtNode, shortExtNode, extListRlpBytes, extValues,
				key[keyIndex], key[keyIndex], branchC16, branchC1, false, false, true, false, false)

			setExtNodeSelectors(extNodeSelectors1, shortExtNode, int(numberOfNibbles1), branchC16)
		*/
		// extNodeSelectors1 = append(extNodeSelectors1, 25)
	} /* else {
		if len1 > len2 {
			// Needed only for len1 > len2
			(*rows)[len(*rows)-branchRows-9][driftedPos] = longNibbles[numberOfNibbles]
		}

		extNodeSelectors1 = append(extNodeSelectors1, 25)
	}
	*/

	// The shortened extension node is needed as a witness to be able to check in a circuit
	// that the shortened extension node and newly added leaf (that causes newly inserted
	// extension node) are the only nodes in the newly inserted extension node.
	/*
	*rows = append(*rows, extNodeSelectors1)
	*rows = append(*rows, extensionRowS1)
	*rows = append(*rows, extensionRowC1)
	 */

	listRlpBytes := [2][]byte{extListRlpBytesS, extListRlpBytesC}
	modExtensionNode := ModExtensionNode{
		ListRlpBytes: listRlpBytes,
	}

	var values [][]byte
	extValuesS = append(extValuesS[:1], extValuesS[2:]...)
	extValuesC = append(extValuesC[:1], extValuesC[2:]...)
	values = append(values, extValuesS...)
	values = append(values, extValuesC...)

	keccakData := [][]byte{}
	keccakData = append(keccakData, longExtNode)
	keccakData = append(keccakData, shortExtNode)

	return Node{
		ModExtension: &modExtensionNode,
		Values:       values,
		KeccakData:   keccakData,
	}
}
