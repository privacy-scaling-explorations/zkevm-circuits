package witness

import (
	"log"

	"github.com/ethereum/go-ethereum/rlp"
)

// isBranch takes GetProof element and returns whether the element is a branch.
func isBranch(proofEl []byte) bool {
	elems, _, err := rlp.SplitList(proofEl)
	check(err)
	c, err1 := rlp.CountValues(elems)
	check(err1)
	if c != 2 && c != 17 {
		log.Fatal("Proof element is neither leaf or branch")
	}
	return c == 17
}

// prepareBranchWitness takes the rows that are to be filled with branch data and it takes
// a branch as returned by GetProof. There are 19 rows for a branch and prepareBranchWitness
// fills the rows from index 1 to index 16 (index 0 is init, index 17 and 18 are for extension
// node when it applies). The parameter branchStart depends on whether it is S or C branch -
// S occupies the first 34 columns, C occupies the next 34 columns.
// The branch children are positioned each in its own row.
func prepareBranchWitness(rows [][]byte, branch []byte, branchStart int, branchRLPOffset int) {
	branchNodeRLPLen := 2 // we have two positions for RLP meta data
	rowInd := 1
	colInd := branchNodeRLPLen - 1

	i := 0
	insideInd := -1
	for {
		if branchRLPOffset+i == len(branch)-1 { // -1 because of the last 128 (branch value)
			break
		}
		b := branch[branchRLPOffset+i]
		if insideInd == -1 && b == 128 {
			rows[rowInd][branchStart] = b
			rowInd++
		} else if insideInd == -1 && b != 128 {
			if b == 160 {
				insideInd = 32
				colInd = branchNodeRLPLen - 2
			} else {
				// non-hashed node
				insideInd = int(b) - 192
				colInd = branchNodeRLPLen - 2
			}
			rows[rowInd][branchStart+colInd] = b
		} else {
			colInd++
			rows[rowInd][branchStart+colInd] = b
			if insideInd == 1 {
				insideInd = -1
				rowInd++
				colInd = 0
			} else {
				insideInd--
			}
		}

		i++
	}
}

func prepareBranchNode(branch1, branch2, extNode1, extNode2, extListRlpBytes []byte, extValues [][]byte, key, driftedInd,
	branchC16, branchC1 byte, isBranchSPlaceholder, isBranchCPlaceholder, isExtension bool) Node {
	extensionNode := ExtensionNode{
		ListRlpBytes: extListRlpBytes,
	}

	var listRlpBytes [2][]byte
	branch1RLPOffset := 1
	branch2RLPOffset := 1
	listRlpBytes1 := []byte{branch1[0]}
	listRlpBytes2 := []byte{branch2[0]}

	if branch1[0] == 248 { // two RLP bytes
		branch1RLPOffset = 2
	} else if branch1[0] == 249 { // three RLP bytes
		branch1RLPOffset = 3
	}

	if branch2[0] == 248 { // two RLP bytes
		branch2RLPOffset = 2
	} else if branch2[0] == 249 { // three RLP bytes
		branch2RLPOffset = 3
	}

	if branch1[0] == 248 || branch1[0] == 249 {
		listRlpBytes1 = append(listRlpBytes1, branch1[1])
	}
	if branch2[0] == 248 || branch2[0] == 249 {
		listRlpBytes2 = append(listRlpBytes2, branch2[1])
	}

	if branch1[0] == 249 {
		listRlpBytes1 = append(listRlpBytes1, branch1[2])
	}
	if branch2[0] == 249 {
		listRlpBytes2 = append(listRlpBytes2, branch2[2])
	}

	listRlpBytes[0] = listRlpBytes1
	listRlpBytes[1] = listRlpBytes2

	branchNode := BranchNode{
		ModifiedIndex: int(key),
		DriftedIndex:  int(driftedInd),
		ListRlpBytes:  listRlpBytes,
	}

	extensionBranch := ExtensionBranchNode{
		IsExtension:   isExtension,
		IsPlaceholder: [2]bool{isBranchSPlaceholder, isBranchCPlaceholder},
		Extension:     extensionNode,
		Branch:        branchNode,
	}

	values := make([][]byte, 17)
	for i := 0; i < len(values); i++ {
		values[i] = make([]byte, valueLen)
	}
	prepareBranchWitness(values, branch1, 0, branch1RLPOffset)

	// Just to get the modified child:
	rows := make([][]byte, 17)
	for i := 0; i < len(rows); i++ {
		rows[i] = make([]byte, valueLen)
	}
	prepareBranchWitness(rows, branch2, 0, branch2RLPOffset)
	values[0] = rows[1+key]

	values = append(values, extValues...)

	keccakData := [][]byte{branch1, branch2}
	if isExtension {
		keccakData = append(keccakData, extNode1)
		keccakData = append(keccakData, extNode2)
	}
	node := Node{
		ExtensionBranch: &extensionBranch,
		Values:          values,
		KeccakData:      keccakData,
	}

	return node
}

// getDriftedPosition returns the position in branch to which the leaf drifted because another
// leaf has been added to the same slot. This information is stored into a branch init row.
func getDriftedPosition(leafKeyRow []byte, numberOfNibbles int) byte {
	var nibbles []byte
	if leafKeyRow[0] != 248 {
		keyLen := int(leafKeyRow[1] - 128)
		if (leafKeyRow[2] != 32) && (leafKeyRow[2] != 0) { // second term is for extension node
			if leafKeyRow[2] < 32 { // extension node
				nibbles = append(nibbles, leafKeyRow[2]-16)
			} else { // leaf
				nibbles = append(nibbles, leafKeyRow[2]-48)
			}
		}
		for i := 0; i < keyLen-1; i++ { // -1 because the first byte doesn't have any nibbles
			b := leafKeyRow[3+i]
			n1 := b / 16
			n2 := b - n1*16
			nibbles = append(nibbles, n1)
			nibbles = append(nibbles, n2)
		}
	} else {
		keyLen := int(leafKeyRow[2] - 128)
		if (leafKeyRow[3] != 32) && (leafKeyRow[3] != 0) { // second term is for extension node
			if leafKeyRow[3] < 32 { // extension node
				nibbles = append(nibbles, leafKeyRow[3]-16)
			} else { // leaf
				nibbles = append(nibbles, leafKeyRow[3]-48)
			}
		}
		for i := 0; i < keyLen-1; i++ { // -1 because the first byte doesn't have any nibbles
			b := leafKeyRow[4+i]
			n1 := b / 16
			n2 := b - n1*16
			nibbles = append(nibbles, n1)
			nibbles = append(nibbles, n2)
		}
	}

	return nibbles[numberOfNibbles]
}

// addBranchAndPlaceholder adds to the rows a branch and its placeholder counterpart
// (used when one of the proofs have one branch more than the other).
func addBranchAndPlaceholder(proof1, proof2,
	extNibblesS, extNibblesC [][]byte,
	leafRow0, key, neighbourNode []byte,
	keyIndex, extensionNodeInd int,
	additionalBranch, isAccountProof, nonExistingAccountProof,
	isShorterProofLastLeaf bool, branchC16, branchC1 byte, toBeHashed *[][]byte) (bool, bool, int, byte, Node) {
	len1 := len(proof1)
	len2 := len(proof2)

	var node Node

	numberOfNibbles := 0
	var extListRlpBytes []byte
	var extValues [][]byte
	for i := 0; i < 4; i++ {
		extValues = append(extValues, make([]byte, valueLen))
	}

	isExtension := (len1 == len2+2) || (len2 == len1+2)
	if !isExtension {
		if branchC16 == 1 {
			branchC16 = 0
			branchC1 = 1
		} else {
			branchC16 = 1
			branchC1 = 0
		}
	} else {
		var numNibbles byte
		if len1 > len2 {
			numNibbles, extListRlpBytes, extValues = prepareExtensions(extNibblesS, extensionNodeInd, proof1[len1-3], proof1[len1-3])
		} else {
			numNibbles, extListRlpBytes, extValues = prepareExtensions(extNibblesC, extensionNodeInd, proof2[len2-3], proof2[len2-3])
		}
		numberOfNibbles = int(numNibbles)

		if numberOfNibbles%2 == 0 {
			if branchC16 == 1 {
				branchC16 = 0
				branchC1 = 1
			} else {
				branchC16 = 1
				branchC1 = 0
			}
		}
	}

	/*
		For special cases when a new extension node is inserted.

		Imagine you have an extension node at n1 n2 n3 n4 (where each of these is a nibble).
		Let's say this extension node has the following nibbles as the extension: n5 n6 n7.
		So at position n1 n2 n3 n4 n5 n6 n7 there is some branch.
		Now we want to add a leaf at position n1 n2 n3 n4 n5 m1 where m1 != n6.
		The adding algorithm walks through the trie, but it bumps into an extension node where
		it should put this leaf. So a new extension node is added at position n1 n2 n3 n4 which only
		has one nibble: n5. So at n1 n2 n3 n4 n5 we have a branch now. In this branch, at position m we
		have a leaf, while at position n6 we have another extension node with one extension nibble: n7.
		At this position (n7) we have the branch from the original extension node.

		When an extension node is inserted because of the added key, C proof will contain this new
		extension node and the underlying branch. However, S proof will stop at the old extension node.
		This old extension node is not part of the C proof, but we need to ensure that it is in the C trie.
		We need to take into account that in the C trie the old extension node has a shortened extension.

		The problem is where to store the old extension node. Note that in the above code the new
		extension node and the underlying branch rows are prepared. For example, when len2 > len1 we
		take extension node from proof2[len2 - 3] and branch from proof2[len2 - 2]. In this case,
		the old extension node in proof1[len1 - 1] has been ignored. For this reason we store it
		in the rows before we add a leaf.
	*/
	var longExtNode []byte
	if len1 > len2 {
		longExtNode = proof2[len2-1]
	} else {
		longExtNode = proof1[len1-1]
	}

	// TODO: fix
	var extNode []byte
	if isExtension {
		if len1 > len2 {
			extNode = proof1[len1-3]
		} else {
			extNode = proof2[len2-3]
		}
	}

	// Note that isModifiedExtNode happens also when we have a branch instead of shortExtNode
	isModifiedExtNode := !isBranch(longExtNode) && !isShorterProofLastLeaf

	if len1 > len2 {
		// We now get the first nibble of the leaf that was turned into branch.
		// This first nibble presents the position of the leaf once it moved
		// into the new branch.
		driftedInd := getDriftedPosition(leafRow0, numberOfNibbles)

		node = prepareBranchNode(proof1[len1-2], proof1[len1-2], extNode, extNode, extListRlpBytes, extValues,
			key[keyIndex+numberOfNibbles], driftedInd,
			branchC16, branchC1, false, true, isExtension)

		// We now get the first nibble of the leaf that was turned into branch.
		// This first nibble presents the position of the leaf once it moved
		// into the new branch.
	} else {
		// We now get the first nibble of the leaf that was turned into branch.
		// This first nibble presents the position of the leaf once it moved
		// into the new branch.
		driftedInd := getDriftedPosition(leafRow0, numberOfNibbles)

		node = prepareBranchNode(proof2[len2-2], proof2[len2-2], extNode, extNode, extListRlpBytes, extValues,
			key[keyIndex+numberOfNibbles], driftedInd,
			branchC16, branchC1, true, false, isExtension)
	}

	return isModifiedExtNode, isExtension, numberOfNibbles, branchC16, node
}
