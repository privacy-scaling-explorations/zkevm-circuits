package witness

import (
	"main/gethutil/mpt/state"
	"main/gethutil/mpt/trie"

	"github.com/ethereum/go-ethereum/common"
)

// equipLeafWithModExtensionNode adds rows for a modified extension node before and after modification.
// These rows are added only when an existing extension node gets shortened or elongated (in terms
// of the extension node nibbles) because of another extension node being added or deleted.
// The rows added are somewhat exceptional as otherwise they do not appear.
func equipLeafWithModExtensionNode(statedb *state.StateDB, leafNode Node, addr common.Address, proof1, proof2,
	extNibblesS, extNibblesC [][]byte,
	key []byte, keyIndex, numberOfNibbles int, isAccountProof bool) Node {
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

	_, extListRlpBytesS, extValuesS := prepareExtensions(extNibbles[len(extNibbles)-1], longExtNode, longExtNode)

	// Get nibbles of the extension node that gets shortened because of the newly insertd
	// extension node:
	longNibbles := getExtensionNodeNibbles(longExtNode)

	ind := byte(keyIndex) + byte(numberOfNibbles) // where the old and new extension nodes start to be different
	longExtNodeKey := make([]byte, len(key))
	copy(longExtNodeKey, key)
	// We would like to retrieve the shortened extension node from the trie via GetProof or
	// GetStorageProof (depending whether it is an account proof or storage proof),
	// the key where we find its underlying branch is `oldExtNodeKey`.
	for j := ind; int(j) < keyIndex+len(longNibbles); j++ {
		// keyIndex is where the nibbles of the old and new extension node start
		longExtNodeKey[j] = longNibbles[j-byte(keyIndex)]
	}

	// There is no short extension node when `len(longNibbles) - numberOfNibbles = 1`, in this case there
	// is simply a branch instead.
	shortExtNodeIsBranch := len(longNibbles)-numberOfNibbles == 1

	var shortExtNode []byte
	var extListRlpBytesC []byte
	var extValuesC [][]byte

	if !shortExtNodeIsBranch {
		k := trie.HexToKeybytes(longExtNodeKey)
		ky := common.BytesToHash(k)
		var proof [][]byte
		var err error
		if isAccountProof {
			proof, _, _, _, _, err = statedb.GetProof(addr)
		} else {
			proof, _, _, _, _, err = statedb.GetStorageProof(addr, ky)
		}
		check(err)

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

		_, extListRlpBytesC, extValuesC = prepareExtensions(extNibbles[len(extNibbles)-1], shortExtNode, shortExtNode)
	} else {
		// When the short node is a branch (and not an extension node), we have nothing to be put in
		// the C extension node witness (as a short node). We copy the long node (S extension node) to let
		// the circuit know that the short node is a branch (the circuit checks whether long node RLC == short node RLC).
		extValuesC = append(extValuesC, make([]byte, valueLen))
		extValuesC = append(extValuesC, make([]byte, valueLen))
		extValuesC = append(extValuesC, make([]byte, valueLen))
		extValuesC = append(extValuesC, make([]byte, valueLen))
		copy(extValuesC[0], extValuesS[0])
		copy(extValuesC[1], extValuesS[1])
		copy(extValuesC[2], extValuesS[2])
		copy(extValuesC[3], extValuesS[3])

		extListRlpBytesC = extListRlpBytesS
	}

	listRlpBytes := [2][]byte{extListRlpBytesS, extListRlpBytesC}

	var values [][]byte
	extValuesS = append(extValuesS[:1], extValuesS[2:]...)
	extValuesC = append(extValuesC[:1], extValuesC[2:]...)
	values = append(values, extValuesS...)
	values = append(values, extValuesC...)

	keccakData := [][]byte{}
	keccakData = append(keccakData, longExtNode)
	keccakData = append(keccakData, shortExtNode)

	if leafNode.Account == nil {
		leafNode.Storage.ModListRlpBytes = listRlpBytes
	} else {
		leafNode.Account.ModListRlpBytes = listRlpBytes
	}

	l := len(leafNode.Values)
	// We put the information about the long and short extension node in the last rows of the leaf
	// An alternative would be to add this information into extension node rows (which are in the branch rows),
	// but this would significantly increase the space needed for every branch.
	for i := 0; i < modifiedExtensionNodeRowLen; i++ {
		leafNode.Values[l-modifiedExtensionNodeRowLen+i] = values[i]
	}

	leafNode.KeccakData = append(leafNode.KeccakData, keccakData...)

	return leafNode
}
