package witness

// setExtNodeSelectors sets in the branch init row the information about the extension node.
func setExtNodeSelectors(row, proofEl []byte, numberOfNibbles int, branchC16 byte) {
	row[isExtensionPos] = 1
	if len(proofEl) > 56 { // 56 because there is 1 byte for length
		// isCExtLongerThan55 doesn't need to be set here
		row[isSExtLongerThan55Pos] = 1
	}

	if len(proofEl) < 32 {
		// isExtNodeSNonHashed doesn't need to be set here
		row[isExtNodeSNonHashedPos] = 1
	}

	if numberOfNibbles == 1 {
		if branchC16 == 1 {
			row[isExtShortC16Pos] = 1
		} else {
			row[isExtShortC1Pos] = 1
		}
	} else {
		if numberOfNibbles%2 == 0 {
			if branchC16 == 1 {
				row[isExtLongEvenC16Pos] = 1
			} else {
				row[isExtLongEvenC1Pos] = 1
			}
		} else {
			if branchC16 == 1 {
				row[isExtLongOddC16Pos] = 1
			} else {
				row[isExtLongOddC1Pos] = 1
			}
		}
	}
}

func prepareEmptyExtensionRows(beforeModification, afterModification bool) [][]byte {
	ext_row1 := make([]byte, rowLen)
	ext_row2 := make([]byte, rowLen)
	if !beforeModification && !afterModification {
		ext_row1 = append(ext_row1, 16)
		ext_row2 = append(ext_row2, 17)
	} else if beforeModification {
		ext_row1 = append(ext_row1, 20)
		ext_row2 = append(ext_row2, 21)
	} else if afterModification {
		ext_row1 = append(ext_row1, 22)
		ext_row2 = append(ext_row2, 23)
	}

	return [][]byte{ext_row1, ext_row2}
}

// TODO: remove when Nodes are fully implemented
func prepareExtensionRows(extNibbles [][]byte, extensionNodeInd int, proofEl1, proofEl2 []byte, beforeModification, afterModification bool) (byte, []byte, []byte) {
	var extensionRowS []byte
	var extensionRowC []byte

	extRows := prepareEmptyExtensionRows(beforeModification, afterModification)
	extensionRowS = extRows[0]
	extensionRowC = extRows[1]
	prepareExtensionRow(extensionRowS, proofEl1, true)
	prepareExtensionRow(extensionRowC, proofEl2, false)

	evenNumberOfNibbles := proofEl1[2] == 0
	keyLen := getExtensionNodeKeyLen(proofEl1)
	numberOfNibbles := getExtensionNumberOfNibbles(proofEl1)

	// We need nibbles as witness to compute key RLC, so we set them
	// into extensionRowC s_advices (we can do this because both extension
	// nodes have the same key, so we can have this info only in one).
	// There can be more up to 64 nibbles, but there is only 32 bytes
	// in extensionRowC s_advices. So we store every second nibble (having
	// the whole byte and one nibble is enough to compute the other nibble).
	startNibblePos := 2 // we don't need any nibbles for case keyLen = 1
	if keyLen > 1 {
		if evenNumberOfNibbles {
			startNibblePos = 1
		} else {
			startNibblePos = 2
		}
	}
	ind := 0
	for j := startNibblePos; j < len(extNibbles[extensionNodeInd]); j += 2 {
		extensionRowC[branchNodeRLPLen+ind] =
			extNibbles[extensionNodeInd][j]
		ind++
	}

	return numberOfNibbles, extensionRowS, extensionRowC
}

func prepareExtensions(extNibbles [][]byte, extensionNodeInd int, proofEl1, proofEl2 []byte) (byte, []byte, [][]byte) {
	var values [][]byte
	v1 := make([]byte, valueLen)
	v2 := make([]byte, valueLen)
	v3 := make([]byte, valueLen)
	v4 := make([]byte, valueLen)

	listRlpBytes := prepareExtension(v1, v2, proofEl1, true)
	prepareExtension(v3, v4, proofEl2, false)

	evenNumberOfNibbles := proofEl1[2] == 0
	keyLen := getExtensionNodeKeyLen(proofEl1)
	numberOfNibbles := getExtensionNumberOfNibbles(proofEl1)

	// We need nibbles as witness to compute key RLC, so we set them
	// into extensionRowC s_advices (we can do this because both extension
	// nodes have the same key, so we can have this info only in one).
	// There can be more up to 64 nibbles, but there is only 32 bytes
	// in extensionRowC s_advices. So we store every second nibble (having
	// the whole byte and one nibble is enough to compute the other nibble).

	startNibblePos := 2 // we don't need any nibbles for case keyLen = 1
	if keyLen > 1 {
		if evenNumberOfNibbles {
			startNibblePos = 1
		} else {
			startNibblePos = 2
		}
	}
	ind := 0
	for j := startNibblePos; j < len(extNibbles[extensionNodeInd]); j += 2 {
		v3[2+ind] = // TODO: check 2 + ind
			extNibbles[extensionNodeInd][j]
		ind++
	}
	values = append(values, v1)
	values = append(values, v2)
	values = append(values, v3)
	values = append(values, v4)

	return numberOfNibbles, listRlpBytes, values
}

func getExtensionLenStartKey(proofEl []byte) (int, int) {
	lenKey := 0
	startKey := 0
	// proofEl[1] <= 32 means only one nibble: the stored value is `16 + nibble`, note that if there are
	// at least two nibbles there will be `128 + number of bytes occupied by nibbles` in proofEl[1]
	if proofEl[1] <= 32 {
		lenKey = 1
		startKey = 1
	} else if proofEl[0] <= 247 {
		lenKey = int(proofEl[1] - 128)
		startKey = 2
	} else {
		lenKey = int(proofEl[2] - 128)
		startKey = 3
	}

	return lenKey, startKey
}

func getExtensionNodeKeyLen(proofEl []byte) byte {
	if proofEl[1] <= 32 {
		return 1
	} else if proofEl[0] <= 247 {
		return proofEl[1] - 128
	} else {
		return proofEl[2] - 128
	}
}

func getExtensionNumberOfNibbles(proofEl []byte) byte {
	evenNumberOfNibbles := proofEl[2] == 0
	numberOfNibbles := byte(0)
	keyLen := getExtensionNodeKeyLen(proofEl)
	if keyLen == 1 {
		numberOfNibbles = 1
	} else if keyLen > 1 && evenNumberOfNibbles {
		numberOfNibbles = (keyLen - 1) * 2
	} else if keyLen > 1 && !evenNumberOfNibbles {
		numberOfNibbles = (keyLen-1)*2 + 1
	}

	return numberOfNibbles
}

func getExtensionNodeNibbles(proofEl []byte) []byte {
	lenKey, startKey := getExtensionLenStartKey(proofEl)

	var nibbles []byte
	if proofEl[startKey] != 0 {
		nibbles = append(nibbles, proofEl[startKey]-16)
	}
	for i := 0; i < lenKey-1; i++ { // -1 because the first byte doesn't have any nibbles
		b := proofEl[startKey+1+i]
		n1 := b / 16
		n2 := b - n1*16
		nibbles = append(nibbles, n1)
		nibbles = append(nibbles, n2)
	}

	return nibbles
}

// TODO: remove when Nodes are fully implemented
func prepareExtensionRow(witnessRow, proofEl []byte, setKey bool) {
	// storageProof[i]:
	// [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
	// Note that the first element (228 in this case) can go much higher - for example, if there
	// are 40 nibbles, this would take 20 bytes which would make the first element 248.

	// If only one nibble in key:
	// [226,16,160,172,105,12...
	// Could also be non-hashed branch:
	// [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128,128,128]

	// Extension node with non-hashed branch:
	// List contains up to 55 bytes (192 + 55)
	// [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

	// List contains more than 55 bytes
	// [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

	// Note that the extension node can be much shorter than the one above - in case when
	// there are less nibbles, so we cannot say that 226 appears as the first byte only
	// when there are hashed nodes in the branch and there is only one nibble.
	// Branch with two non-hashed nodes (that's the shortest possible branch):
	// [217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
	// Note: branch contains at least 26 bytes. 192 + 26 = 218

	/*
		If proofEl[0] <= 247 (length at most 55, so proofEl[1] doesn't specify the length of the whole
			remaining stream, only of the next substream)
		  If proofEl[1] <= 128:
		    There is only 1 byte for nibbles (keyLen = 1) and this is proofEl[1].
		  Else:
		    Nibbles are stored in more than 1 byte, proofEl[1] specifies the length of bytes.
		Else:
		  proofEl[1] contains the length of the remaining stream.
		  proofEl[2] specifies the length of the bytes (for storing nibbles).
		  Note that we can't have only one nibble in this case.
	*/

	if setKey {
		witnessRow[0] = proofEl[0]
		witnessRow[1] = proofEl[1]
	}

	lenKey, startKey := getExtensionLenStartKey(proofEl)
	if startKey == 3 {
		witnessRow[2] = proofEl[2]
	}

	if setKey {
		for j := 0; j < lenKey; j++ {
			witnessRow[startKey+j] = proofEl[startKey+j]
		}
	}

	encodedNodeLen := proofEl[startKey+lenKey]
	nodeLen := byte(0)
	start := branch2start
	if encodedNodeLen > 192 {
		// we have a list, that means a non-hashed node
		nodeLen = encodedNodeLen - 192
	} else if encodedNodeLen == 160 {
		// hashed-node
		nodeLen = encodedNodeLen - 128
	}
	witnessRow[start] = encodedNodeLen
	for j := 0; j < int(nodeLen); j++ {
		witnessRow[start+1+j] = proofEl[startKey+lenKey+1+j]
	}
}

func prepareExtension(v1, v2, proofEl []byte, setKey bool) []byte {
	// storageProof[i]:
	// [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
	// Note that the first element (228 in this case) can go much higher - for example, if there
	// are 40 nibbles, this would take 20 bytes which would make the first element 248.

	// If only one nibble in key:
	// [226,16,160,172,105,12...
	// Could also be non-hashed branch:
	// [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128,128,128]

	// Extension node with non-hashed branch:
	// List contains up to 55 bytes (192 + 55)
	// [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

	// List contains more than 55 bytes
	// [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

	// Note that the extension node can be much shorter than the one above - in case when
	// there are less nibbles, so we cannot say that 226 appears as the first byte only
	// when there are hashed nodes in the branch and there is only one nibble.
	// Branch with two non-hashed nodes (that's the shortest possible branch):
	// [217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
	// Note: branch contains at least 26 bytes. 192 + 26 = 218

	/*
		If proofEl[0] <= 247 (length at most 55, so proofEl[1] doesn't specify the length of the whole
			remaining stream, only of the next substream)
		  If proofEl[1] <= 128:
		    There is only 1 byte for nibbles (keyLen = 1) and this is proofEl[1].
		  Else:
		    Nibbles are stored in more than 1 byte, proofEl[1] specifies the length of bytes.
		Else:
		  proofEl[1] contains the length of the remaining stream.
		  proofEl[2] specifies the length of the bytes (for storing nibbles).
		  Note that we can't have only one nibble in this case.
	*/

	var listRlpBytes []byte
	listRlpBytes = append(listRlpBytes, proofEl[0])

	lenKey, startKey := getExtensionLenStartKey(proofEl)
	if lenKey != 1 {
		// The descriptor now contains the key length RLP in value row:
		startKey = startKey - 1
		lenKey = lenKey + 1
	}

	// TODO
	if startKey == 3 {
		listRlpBytes = append(listRlpBytes, proofEl[1])
	}

	if setKey {
		for j := 0; j < lenKey; j++ {
			v1[j] = proofEl[startKey+j]
		}
	}

	encodedNodeLen := proofEl[startKey+lenKey]
	nodeLen := byte(0)
	if encodedNodeLen > 192 {
		// we have a list, that means a non-hashed node
		nodeLen = encodedNodeLen - 192
	} else if encodedNodeLen == 160 {
		// hashed-node
		nodeLen = encodedNodeLen - 128
	}
	v2[0] = encodedNodeLen
	for j := 0; j < int(nodeLen); j++ {
		v2[1+j] = proofEl[startKey+lenKey+1+j]
	}

	return listRlpBytes
}
