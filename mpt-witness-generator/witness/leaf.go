package witness

import (
	"math"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/trie"
)

func prepareEmptyNonExistingStorageRow() []byte {
	// nonExistingStorageRow is used only for proof that nothing is stored at a particular storage key
	nonExistingStorageRow := make([]byte, valueLen)

	return nonExistingStorageRow
}

func prepareNonExistingStorageRow(leafC, keyNibbles []byte, noLeaf bool) ([]byte, []byte) {
	// nonExistingStorageRow is used only for proof that nothing is stored at a particular storage key
	nonExistingStorageRow := prepareEmptyNonExistingStorageRow()

	var wrongRlpBytes []byte
	wrongRlpBytes = append(wrongRlpBytes, leafC[0])
	start := 2
	if leafC[0] == 248 {
		start = 3
		wrongRlpBytes = append(wrongRlpBytes, leafC[1])
	}
	keyLenC := int(leafC[start-1]) - 128
	keyRowC := make([]byte, valueLen)
	for i := 0; i < keyLenC; i++ {
		keyRowC[i] = leafC[start-1+i]
	}

	offset := 0
	nibblesNum := (keyLenC - 1) * 2

	nonExistingStorageRow[0] = leafC[start-1]
	if keyRowC[1] != 32 { // odd number of nibbles
		nibblesNum = nibblesNum + 1
		nonExistingStorageRow[1] = keyNibbles[64-nibblesNum] + 48
		offset = 1
	} else {
		nonExistingStorageRow[1] = 32
	}
	// Get the last nibblesNum of address:
	remainingNibbles := keyNibbles[64-nibblesNum : 64] // exclude the last one as it is not a nibble
	for i := 0; i < keyLenC-1; i++ {
		nonExistingStorageRow[2+i] = remainingNibbles[2*i+offset]*16 + remainingNibbles[2*i+1+offset]
	}

	return wrongRlpBytes, nonExistingStorageRow
}

func getNonceBalanceValue(leaf []byte, keyLen int) ([]byte, []byte, int) {
	nonceStart := 3 + keyLen + 1 + 1 + 1 + 1

	var nonceRlpLen byte
	var balanceStart int
	var nonce []byte

	// If the first nonce byte is > 128, it means it presents (nonce_len - 128),
	// if the first nonce byte is <= 128, the actual nonce value is < 128 and is exactly this first byte
	// (however, when nonce = 0, the actual value that is stored is 128)
	if leaf[nonceStart] <= 128 {
		// only one nonce byte
		nonceRlpLen = 1
		nonce = leaf[nonceStart : nonceStart+int(nonceRlpLen)]
		balanceStart = nonceStart + int(nonceRlpLen)
	} else {
		nonceRlpLen = leaf[nonceStart] - 128
		nonce = leaf[nonceStart : nonceStart+int(nonceRlpLen)+1]
		balanceStart = nonceStart + int(nonceRlpLen) + 1
	}

	var balanceRlpLen byte
	var storageStart int
	if leaf[balanceStart] <= 128 {
		// only one balance byte
		balanceRlpLen = 1
		storageStart = balanceStart + int(balanceRlpLen)
	} else {
		balanceRlpLen = leaf[balanceStart] - 128
		storageStart = balanceStart + int(balanceRlpLen) + 1
	}

	nonceVal := make([]byte, valueLen)
	balanceVal := make([]byte, valueLen)
	copy(nonceVal, nonce)
	var balance []byte
	if balanceRlpLen == 1 {
		balance = leaf[balanceStart : balanceStart+int(balanceRlpLen)]
	} else {
		balance = leaf[balanceStart : balanceStart+int(balanceRlpLen)+1]
	}
	copy(balanceVal, balance)

	return nonceVal, balanceVal, storageStart
}

func getStorageRootCodeHashValue(leaf []byte, storageStart int) ([]byte, []byte) {
	storageRootValue := make([]byte, valueLen)
	codeHashValue := make([]byte, valueLen)
	storageRlpLen := leaf[storageStart] - 128
	if storageRlpLen != 32 {
		panic("Account leaf RLP 3")
	}
	storage := leaf[storageStart : storageStart+32+1]
	for i := 0; i < 33; i++ {
		storageRootValue[i] = storage[i]
	}
	codeHashStart := storageStart + int(storageRlpLen) + 1
	codeHashRlpLen := leaf[codeHashStart] - 128
	if codeHashRlpLen != 32 {
		panic("Account leaf RLP 4")
	}
	codeHash := leaf[codeHashStart : codeHashStart+32+1]
	for i := 0; i < 33; i++ {
		codeHashValue[i] = codeHash[i]
	}

	return storageRootValue, codeHashValue
}

func prepareAccountLeafNode(addr common.Address, addrh []byte, leafS, leafC, neighbourNode, addressNibbles []byte, isPlaceholder, isSModExtension, isCModExtension bool) Node {
	// For non existing account proof there are two cases:
	// 1. A leaf is returned that is not at the required address (wrong leaf).
	// 2. A branch is returned as the last element of getProof and
	//    there is nil object at address position. Placeholder account leaf is added in this case.
	values := make([][]byte, 12)

	keyLenS := int(leafS[2]) - 128
	keyLenC := int(leafC[2]) - 128
	keyRowS := make([]byte, valueLen)
	keyRowC := make([]byte, valueLen)

	for i := 2; i < 3+keyLenS; i++ {
		keyRowS[i-2] = leafS[i]
	}
	for i := 2; i < 3+keyLenC; i++ {
		keyRowC[i-2] = leafC[i]
	}

	var listRlpBytes [2][]byte
	listRlpBytes[0] = make([]byte, 2)
	listRlpBytes[1] = make([]byte, 2)
	for i := 0; i < 2; i++ {
		listRlpBytes[0][i] = leafS[i]
	}
	for i := 0; i < 2; i++ {
		listRlpBytes[1][i] = leafC[i]
	}

	var valueRlpBytes [2][]byte
	valueRlpBytes[0] = make([]byte, 2)
	valueRlpBytes[1] = make([]byte, 2)

	var valueListRlpBytes [2][]byte
	valueListRlpBytes[0] = make([]byte, 2)
	valueListRlpBytes[1] = make([]byte, 2)

	driftedRlpBytes := []byte{0}
	keyDrifted := make([]byte, valueLen)
	if neighbourNode != nil {
		keyDrifted, _, driftedRlpBytes, _ = prepareStorageLeafInfo(neighbourNode, false, false)
	}

	wrongValue := make([]byte, valueLen)
	wrongRlpBytes := make([]byte, 2)

	// For non existing account proof, keyRowS (=keyRowC in this case) stores the key of
	// the wrong leaf. We store the key of the required leaf (which doesn't exist)
	// in nonExistingAccountRow.

	// wrongValue is used only for proof that account doesn't exist

	offset := 0
	nibblesNum := (keyLenC - 1) * 2
	wrongRlpBytes[0] = leafC[0]
	wrongRlpBytes[1] = leafC[1]
	wrongValue[0] = leafC[2] // length
	if leafC[3] != 32 {      // odd number of nibbles
		nibblesNum = nibblesNum + 1
		wrongValue[1] = addressNibbles[64-nibblesNum] + 48
		offset = 1
	} else {
		wrongValue[1] = 32
	}
	// Get the last nibblesNum of address:
	remainingNibbles := addressNibbles[64-nibblesNum : 64] // exclude the last one as it is not a nibble
	for i := 0; i < keyLenC-1; i++ {
		wrongValue[2+i] = remainingNibbles[2*i+offset]*16 + remainingNibbles[2*i+1+offset]
	}

	rlpStringSecondPartLenS := leafS[3+keyLenS] - 183
	if rlpStringSecondPartLenS != 1 {
		panic("Account leaf RLP at this position should be 1 (S)")
	}
	rlpStringSecondPartLenC := leafC[3+keyLenC] - 183
	if rlpStringSecondPartLenC != 1 {
		panic("Account leaf RLP at this position should be 1 (C)")
	}
	rlpStringLenS := leafS[3+keyLenS+1]
	rlpStringLenC := leafC[3+keyLenC+1]

	// [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80,248,78
	// In this example RLP, there are first 36 bytes of a leaf.
	// 157 means there are 29 bytes for key (157 - 128).
	// Positions 32-35: 184, 80, 248, 78.
	// 184 - 183 = 1 means length of the second part of a string.
	// 80 means length of a string.
	// 248 - 247 = 1 means length of the second part of a list.
	// 78 means length of a list.

	rlpListSecondPartLenS := leafS[3+keyLenS+1+1] - 247
	if rlpListSecondPartLenS != 1 {
		panic("Account leaf RLP 1 (S)")
	}
	rlpListSecondPartLenC := leafC[3+keyLenC+1+1] - 247
	if rlpListSecondPartLenC != 1 {
		panic("Account leaf RLP 1 (C)")
	}

	rlpListLenS := leafS[3+keyLenS+1+1+1]
	if rlpStringLenS != rlpListLenS+2 {
		panic("Account leaf RLP 2 (S)")
	}

	rlpListLenC := leafC[3+keyLenC+1+1+1]
	if rlpStringLenC != rlpListLenC+2 {
		panic("Account leaf RLP 2 (C)")
	}

	storageStartS := 0
	storageStartC := 0
	nonceValueS := make([]byte, valueLen)
	nonceValueC := make([]byte, valueLen)
	balanceValueS := make([]byte, valueLen)
	balanceValueC := make([]byte, valueLen)
	if !isPlaceholder {
		nonceValueS, balanceValueS, storageStartS = getNonceBalanceValue(leafS, keyLenS)
		nonceValueC, balanceValueC, storageStartC = getNonceBalanceValue(leafC, keyLenC)
	}

	valueRlpBytes[0][0] = leafS[3+keyLenS]
	valueRlpBytes[0][1] = leafS[3+keyLenS+1]

	valueRlpBytes[1][0] = leafC[3+keyLenC]
	valueRlpBytes[1][1] = leafC[3+keyLenC+1]

	valueListRlpBytes[0][0] = leafS[3+keyLenS+1+1]
	valueListRlpBytes[0][1] = leafS[3+keyLenS+1+1+1]

	valueListRlpBytes[1][0] = leafC[3+keyLenC+1+1]
	valueListRlpBytes[1][1] = leafC[3+keyLenC+1+1+1]

	storageRootValueS := make([]byte, valueLen)
	storageRootValueC := make([]byte, valueLen)
	codeHashValueS := make([]byte, valueLen)
	codeHashValueC := make([]byte, valueLen)
	if !isPlaceholder {
		storageRootValueS, codeHashValueS = getStorageRootCodeHashValue(leafS, storageStartS)
		storageRootValueC, codeHashValueC = getStorageRootCodeHashValue(leafC, storageStartC)
	}

	values[AccountKeyS] = keyRowS
	values[AccountKeyC] = keyRowC
	values[AccountNonceS] = nonceValueS
	values[AccountBalanceS] = balanceValueS
	values[AccountStorageS] = storageRootValueS
	values[AccountCodehashS] = codeHashValueS
	values[AccountNonceC] = nonceValueC
	values[AccountBalanceC] = balanceValueC
	values[AccountStorageC] = storageRootValueC
	values[AccountCodehashC] = codeHashValueC
	values[AccountDrifted] = keyDrifted
	values[AccountWrong] = wrongValue
	
	for i := 0; i < 6; i++ {
		row := make([]byte, valueLen)
		values = append(values, row)
	}

	leaf := AccountNode{
		Address:           addr,
		Key:               addrh,
		ListRlpBytes:      listRlpBytes,
		ValueRlpBytes:     valueRlpBytes,
		ValueListRlpBytes: valueListRlpBytes,
		DriftedRlpBytes:   driftedRlpBytes,
		WrongRlpBytes:     wrongRlpBytes,
		IsModExtension:    [2]bool{isSModExtension, isCModExtension},
	}
	keccakData := [][]byte{leafS, leafC, addr.Bytes()}
	if neighbourNode != nil {
		keccakData = append(keccakData, neighbourNode)
	}
	node := Node{
		Account:    &leaf,
		Values:     values,
		KeccakData: keccakData,
	}

	return node
}

// prepareLeafAndPlaceholderNode prepares a leaf node and its placeholder counterpart
// (used when one of the proofs does not have a leaf).
func prepareLeafAndPlaceholderNode(addr common.Address, addrh []byte, proof1, proof2 [][]byte, storage_key common.Hash, key []byte, nonExistingAccountProof, isAccountProof, isSModExtension, isCModExtension bool) Node {
	len1 := len(proof1)
	len2 := len(proof2)

	// We don't have a leaf in the shorter proof, but we will add it there
	// as a placeholder.
	if isAccountProof {
		var leafS []byte
		var leafC []byte
		if len1 > len2 {
			leafS = proof1[len1-1]
			leafC = proof1[len1-1] // placeholder
		} else {
			leafC = proof2[len2-1]
			leafS = proof2[len2-1] // placeholder
		}

		// When generating a proof that account doesn't exist, the length of both proofs is the same (doesn't reach
		// this code).
		return prepareAccountLeafNode(addr, addrh, leafS, leafC, nil, key, false, isSModExtension, isCModExtension)
	} else {
		var leaf []byte
		isSPlaceholder := false
		isCPlaceholder := false

		if len1 > len2 {
			leaf = proof1[len1-1]
			isCPlaceholder = true
		} else {
			leaf = proof2[len2-1]
			isSPlaceholder = true
		}

		return prepareStorageLeafNode(leaf, leaf, nil, storage_key, key, false, isSPlaceholder, isCPlaceholder, isSModExtension, isCModExtension)
	}
}

// getLeafKeyLen returns the leaf key length given the key index (how many key nibbles have
// been used in the branches / extension nodes above the leaf).
func getLeafKeyLen(keyIndex int) int {
	return int(math.Floor(float64(64-keyIndex)/float64(2))) + 1
}

// setStorageLeafKeyRLP sets the RLP byte that encodes key length of the storage leaf
// to correspond to the number of keys used in the branches / extension nodes above the placeholder leaf.
func setStorageLeafKeyRLP(leaf *[]byte, key []byte, keyIndex int) {
	isEven := keyIndex%2 == 0
	remainingNibbles := key[keyIndex:]
	keyLen := getLeafKeyLen(keyIndex)
	(*leaf)[1] = byte(keyLen) + 128
	if isEven {
		(*leaf)[2] = 32
	} else {
		(*leaf)[2] = remainingNibbles[0] + 48
	}
}

func prepareAccountLeafPlaceholderNode(addr common.Address, addrh, key []byte, keyIndex int) Node {
	isEven := keyIndex%2 == 0
	keyLen := int(math.Floor(float64(64-keyIndex)/float64(2))) + 1
	remainingNibbles := key[keyIndex:]
	offset := 0
	leaf := make([]byte, 40)
	leaf[0] = 248
	leaf[1] = byte(keyLen) + 73
	leaf[2] = byte(keyLen) + 128
	leaf[3+keyLen] = 184
	leaf[3+keyLen+1+1] = 248
	leaf[3+keyLen+1+1+1] = leaf[3+keyLen+1] - 2
	if isEven {
		leaf[3] = 32
	} else {
		leaf[3] = remainingNibbles[0] + 48
		offset = 1
	}
	for i := 0; i < keyLen-1; i++ {
		leaf[4+i] = remainingNibbles[2*i+offset]*16 + remainingNibbles[2*i+1+offset]
	}

	node := prepareAccountLeafNode(addr, addrh, leaf, leaf, nil, key, true, false, false)

	node.Account.ValueRlpBytes[0][0] = 184
	node.Account.ValueRlpBytes[0][1] = 70
	node.Account.ValueRlpBytes[1][0] = 184
	node.Account.ValueRlpBytes[1][1] = 70

	node.Account.ValueListRlpBytes[0][0] = 248
	node.Account.ValueListRlpBytes[0][1] = 68
	node.Account.ValueListRlpBytes[1][0] = 248
	node.Account.ValueListRlpBytes[1][1] = 68

	node.Values[AccountStorageS][0] = 160
	node.Values[AccountStorageC][0] = 160
	node.Values[AccountCodehashS][0] = 160
	node.Values[AccountCodehashC][0] = 160

	return node
}

func prepareStorageLeafPlaceholderNode(storage_key common.Hash, key []byte, keyIndex int) Node {
	leaf := make([]byte, valueLen)
	setStorageLeafKeyRLP(&leaf, key, keyIndex)
	keyLen := getLeafKeyLen(keyIndex)
	leaf[0] = 192 + 1 + byte(keyLen) + 1

	return prepareStorageLeafNode(leaf, leaf, nil, storage_key, key, false, true, true, false, false)
}

func prepareStorageLeafInfo(row []byte, valueIsZero, isPlaceholder bool) ([]byte, []byte, []byte, []byte) {
	var keyRlp []byte
	var valueRlp []byte
	var keyRlpLen byte
	key := make([]byte, valueLen)
	value := make([]byte, valueLen)

	var setKeyValue = func(keyLen, offset byte) {
		if !isPlaceholder {
			valueRlp = row[keyLen+offset : keyLen+offset+1]
			if !valueIsZero {
				copy(value, row[keyLen+offset+1:])
			}
		} else {
			// If placeholder, we leave the value to be 0.
			valueRlp = []byte{0}
			// We need to take into account that the value is 0, so of length 1.
			// keyRlp holds the RLP of the whole leaf:
			// - (keyLen + 1) is the number of key bytes
			// - 1 is the number of value bytes
			if row[0] == 248 {
				// keyRlp have two bytes, we need to have only one (when value is 0, it's always short)
				keyRlp = []byte{192 + keyLen + 2}
			} else {
				keyRlp[0] = 192 + keyLen + 2
			}
		}
	}

	keyLen := byte(0)
	offset := byte(1)
	if len(row) < 32 { // the node doesn't get hashed in this case
		keyRlpLen = 1
		keyRlp = make([]uint8, keyRlpLen)
		copy(keyRlp, row[:keyRlpLen])

		// 192 + 32 = 224
		if row[1] < 128 {
			// last level: [194,32,1]
			// or
			// only one nibble in a leaf (as soon as the leaf has two nibbles, row[1] will have 128 + length)
			// [194,48,1] - this one contains nibble 0 = 48 - 48
			keyLen = byte(1)
			copy(key, row[keyRlpLen:keyLen+1])
			offset = byte(1)
		} else {
			// [196,130,32,0,1]
			keyLen = row[1] - 128
			copy(key, row[keyRlpLen:keyLen+2])
			offset = byte(2)
		}
	} else if row[0] == 248 {
		// [248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...
		keyRlpLen = 2
		keyLen = row[2] - 128
		keyRlp = row[:keyRlpLen]
		copy(key, row[keyRlpLen:keyLen+3])
		offset = byte(3)
	} else {
		keyRlpLen = 1
		keyRlp = make([]uint8, keyRlpLen)
		copy(keyRlp, row[:keyRlpLen])
		if row[1] < 128 {
			// last level:
			// [227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
			// one nibble:
			// [227,48,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
			key[0] = row[0]
			key[1] = row[1]
			keyLen = byte(2)
			offset = byte(0)
		} else {
			// [226,160,59,138,106,70,105,186,37,13,38[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
			keyLen = row[1] - 128
			copy(key, row[keyRlpLen:keyLen+2])
			offset = byte(2)
		}
	}
	setKeyValue(keyLen, offset)

	return key, value, keyRlp, valueRlp
}

func prepareStorageLeafNode(leafS, leafC, neighbourNode []byte, storage_key common.Hash, key []byte, nonExistingStorageProof, isSPlaceholder, isCPlaceholder, isSModExtension, isCModExtension bool) Node {
	var rows [][]byte

	keyS, valueS, listRlpBytes1, valueRlpBytes1 := prepareStorageLeafInfo(leafS, false, isSPlaceholder)

	rows = append(rows, keyS)
	rows = append(rows, valueS)

	keyC, valueC, listRlpBytes2, valueRlpBytes2 := prepareStorageLeafInfo(leafC, false, isCPlaceholder)

	rows = append(rows, keyC)
	rows = append(rows, valueC)

	var listRlpBytes [2][]byte
	listRlpBytes[0] = listRlpBytes1
	listRlpBytes[1] = listRlpBytes2

	var valueRlpBytes [2][]byte
	valueRlpBytes[0] = valueRlpBytes1
	valueRlpBytes[1] = valueRlpBytes2

	driftedRlpBytes := []byte{0}
	keyDrifted := make([]byte, valueLen)
	if neighbourNode != nil {
		keyDrifted, _, driftedRlpBytes, _ = prepareStorageLeafInfo(neighbourNode, false, false)
	}
	rows = append(rows, keyDrifted)

	var nonExistingStorageRow []byte
	var wrongRlpBytes []byte
	if nonExistingStorageProof {
		noLeaf := false
		wrongRlpBytes, nonExistingStorageRow = prepareNonExistingStorageRow(leafC, key, noLeaf)
	} else {
		nonExistingStorageRow = prepareEmptyNonExistingStorageRow()
	}
	rows = append(rows, nonExistingStorageRow)

	for i := 0; i < 6; i++ {
		row := make([]byte, valueLen)
		rows = append(rows, row)
	}

	leaf := StorageNode{
		Address:         storage_key,
		Key:             trie.HexToKeybytes(key),
		ListRlpBytes:    listRlpBytes,
		DriftedRlpBytes: driftedRlpBytes,
		WrongRlpBytes:   wrongRlpBytes,
		ValueRlpBytes:   valueRlpBytes,
		IsModExtension:  [2]bool{isSModExtension, isCModExtension},
	}
	keccakData := [][]byte{leafS, leafC, storage_key.Bytes()}
	if neighbourNode != nil {
		keccakData = append(keccakData, neighbourNode)
	}
	node := Node{
		Values:     rows,
		Storage:    &leaf,
		KeccakData: keccakData,
	}

	return node
}
