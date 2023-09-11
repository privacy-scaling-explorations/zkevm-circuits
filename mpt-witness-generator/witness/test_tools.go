package witness

import (
	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/trie"
)

// moveAccountFromSecondToFirstLevel moves an account from the second level to the first level (key stored in a leaf
// gets longer). The function is used to enable tests with an account being in the first trie level.
func moveAccountFromSecondToFirstLevel(firstNibble byte, account []byte) []byte {
	newAccount := make([]byte, len(account)+1)
	newAccount[0] = account[0]
	newAccount[1] = account[1] + 1
	newAccount[2] = 161
	newAccount[3] = 32
	// The following code relies on the account being in the second level (and not being
	// after an extension node).
	newAccount[4] = firstNibble*16 + account[3] - 48
	for i := 0; i < 31; i++ {
		newAccount[5+i] = account[4+i]
	}
	for i := 0; i < int(account[1]-33); i++ {
		newAccount[4+32+i] = account[35+i]
	}

	return newAccount
}

// moveAccountFromThirdToSecondLevel moves the account from the third level to the second level (key stored in a leaf
// gets longer).
func moveAccountFromThirdToSecondLevel(addrh []byte, account []byte) []byte {
	// account = [248, 105, 160, 32, 77, 78,...]
	newAccount := make([]byte, len(account))
	copy(newAccount, account)
	// The following code relies on the account being in the third level (and not being
	// after an extension node).
	posInBranch := addrh[0] % 16
	newAccount[3] = 48 + posInBranch

	return newAccount
}

// modifyAccountSpecialEmptyTrie prepares an account leaf in the first trie level for C proof and
// a placeholder leaf in S proof.
func modifyAccountSpecialEmptyTrie(addrh []byte, accountProof1Last []byte) ([][]byte, [][]byte, common.Hash, common.Hash) {
	firstNibble := addrh[0] / 16
	newAccount := moveAccountFromSecondToFirstLevel(firstNibble, accountProof1Last)

	newAccount1 := make([]byte, len(accountProof1Last)+1)
	copy(newAccount1, newAccount)

	accountProof := make([][]byte, 1)
	accountProof[0] = newAccount
	accountProof1 := make([][]byte, 1)
	accountProof1[0] = newAccount1

	// leaf in S proof is a placeholder, thus newAccount needs to have an empty trie hash
	// for the root:
	emptyTrieHash := []byte{86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33}
	rootStart := len(newAccount) - 64 - 1

	for i := 0; i < 32; i++ {
		newAccount[rootStart+i] = emptyTrieHash[i]
	}

	hasher := trie.NewHasher(false)
	sRoot := common.BytesToHash(hasher.HashData(newAccount))
	cRoot := common.BytesToHash(hasher.HashData(newAccount1))

	return accountProof, accountProof1, sRoot, cRoot
}

// modifyAccountProofSpecialTests modifies S and C account proofs to serve for special tests - like moving
// the account leaf in the first trie level.
func modifyAccountProofSpecialTests(addrh, accountAddr []byte, sRoot, cRoot common.Hash, accountProof, accountProof1 [][]byte, aNeighbourNode2 []byte, specialTest byte) ([]byte, []byte, [][]byte, [][]byte, common.Hash, common.Hash) {
	if specialTest == 1 {
		account := accountProof1[len(accountProof1)-1]
		if len(accountProof1) != 2 {
			panic("account should be in the second level (one branch above it)")
		}
		firstNibble := addrh[0] / 16
		newAccount := moveAccountFromSecondToFirstLevel(firstNibble, account)

		newAccount1 := make([]byte, len(account)+1)
		copy(newAccount1, newAccount)

		// change nonce:
		newAccount1[3+33+4] = 1

		accountProof = make([][]byte, 1)
		accountProof[0] = newAccount
		accountProof1 = make([][]byte, 1)
		accountProof1[0] = newAccount1

		hasher := trie.NewHasher(false)
		sRoot = common.BytesToHash(hasher.HashData(newAccount))
		cRoot = common.BytesToHash(hasher.HashData(newAccount1))
	} else if specialTest == 3 {
		if len(accountProof) != 2 && len(accountProof1) != 3 {
			panic("account should be in the second level (one branch above it)")
		}
		accountS := accountProof[len(accountProof)-1]
		account1Pos := addrh[0] / 16
		// driftedPos := ((addrh[0] / 16) + 1) % 16 // something else than the first nibble of addrh
		driftedPos := byte(0) // TODO: remove hardcoding
		// addresses of both account now differ only in the first nibble (this is not needed,
		// it is just in this construction)
		newAccount := moveAccountFromSecondToFirstLevel(driftedPos, accountS)

		hasher := trie.NewHasher(false)

		firstNibble := accountProof[1][3] - 48
		// [248, 81, 128, 128, ...
		branch := accountProof1[len(accountProof1)-2]
		branch1 := make([]byte, len(branch))
		for i := 0; i < len(branch1); i++ {
			branch1[i] = 128
		}
		branch1[0] = branch[0]
		branch1[1] = branch[1]

		// drifted leaf (aNeighbourNode2) has one nibble more after moved one level up, we need to recompute the hash
		fmt.Println(driftedPos)
		aNeighbourNode2[3] = 48 + firstNibble
		driftedLeafHash := common.BytesToHash(hasher.HashData(aNeighbourNode2))
		// branch is now one level higher, both leaves are at different positions now
		// (one nibble to the left)

		branch1[2+int(driftedPos)] = 160
		for i := 0; i < 32; i++ {
			branch1[2+int(driftedPos)+1+i] = driftedLeafHash[i]
		}

		accountC3 := accountProof1[len(accountProof1)-1]
		newAccountC2 := moveAccountFromThirdToSecondLevel(addrh, accountC3)

		driftedLeafHash2 := common.BytesToHash(hasher.HashData(newAccountC2))
		branch1[2+32+int(account1Pos)] = 160
		for i := 0; i < 32; i++ {
			branch1[2+32+int(account1Pos)+1+i] = driftedLeafHash2[i]
		}

		// Let us have placeholder branch in the first level
		accountProof = make([][]byte, 1)
		accountProof[0] = newAccount
		accountProof1 = make([][]byte, 2)
		accountProof1[0] = branch1
		accountProof1[1] = newAccountC2

		sRoot = common.BytesToHash(hasher.HashData(accountProof[0]))
		cRoot = common.BytesToHash(hasher.HashData(accountProof1[0]))
	} else if specialTest == 4 {
		// This test simulates having only one account in the state trie:
		account := []byte{248, 106, 161, 32, 252, 237, 52, 8, 133, 130, 180, 167, 143, 97, 28, 115, 102, 25, 94, 62, 148, 249, 8, 6, 55, 244, 16, 75, 187, 208, 208, 127, 251, 120, 61, 73, 184, 70, 248, 68, 128, 128, 160, 86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33, 160, 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112}

		// Note: the requested address (for which the account doesn't exist) should have
		// a different address as the only one in the trie.

		accountProof = make([][]byte, 1)
		accountProof[0] = account
		accountProof1 = make([][]byte, 1)
		accountProof1[0] = account

		hasher := trie.NewHasher(false)
		sRoot = common.BytesToHash(hasher.HashData(accountProof[0]))
		cRoot = common.BytesToHash(hasher.HashData(accountProof1[0]))
	} else if specialTest == 5 {
		ext := []byte{226, 24, 160, 194, 200, 39, 82, 205, 97, 69, 91, 92, 98, 218, 180, 101, 42, 171, 150, 75, 251, 147, 154, 59, 215, 26, 164, 201, 90, 199, 185, 190, 205, 167, 64}
		branch := []byte{248, 81, 128, 128, 128, 160, 53, 8, 52, 235, 77, 44, 138, 235, 20, 250, 15, 188, 176, 83, 178, 108, 212, 224, 40, 146, 117, 31, 154, 215, 103, 179, 234, 32, 168, 86, 167, 44, 128, 128, 128, 128, 128, 160, 174, 121, 120, 114, 157, 43, 164, 140, 103, 235, 28, 242, 186, 33, 76, 152, 157, 197, 109, 149, 229, 229, 22, 189, 233, 207, 92, 195, 82, 121, 240, 3, 128, 128, 128, 128, 128, 128, 128}
		// The original proof returns `ext` and `branch` in 2. and 3. level. We move them to 1. and 2. level.

		fmt.Println(ext)
		fmt.Println(branch)

		newAddrBytes := make([]byte, 32)
		newAddrNibbles := make([]byte, 65)
		newAddrNibbles[64] = accountAddr[16]
		for i := 0; i < 63; i++ {
			newAddrNibbles[i] = accountAddr[i+1]
		}
		newAddrNibbles[63] = accountAddr[0]

		for i := 0; i < 32; i++ {
			newAddrBytes[i] = newAddrNibbles[2*i]*16 + newAddrNibbles[2*i+1]
		}

		// We need to fix leaf key (adding last nibble):
		// Original leaf:
		// leaf := []byte{248, 104, 159, 59, 114, 3, 66, 104, 61, 61, 61, 175, 101, 56, 194, 213, 150, 208, 62, 118, 28, 175, 138, 112, 119, 76, 88, 109, 21, 102, 195, 8, 18, 185, 184, 70, 248, 68, 128, 128, 160, 86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33, 160, 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112}
		leaf := []byte{248, 105, 160, 32, 59, 114, 3, 66, 104, 61, 61, 61, 175, 101, 56, 194, 213, 150, 208, 62, 118, 28, 175, 138, 112, 119, 76, 88, 109, 21, 102, 195, 8, 18, 185, 184, 70, 248, 68, 128, 128, 160, 86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33, 160, 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112}
		for i := 0; i < 31; i++ {
			leaf[4+i] = newAddrBytes[i+1]
		}

		hasher := trie.NewHasher(false)
		// Update leaf hash in branch
		newLeafHash := common.BytesToHash(hasher.HashData(leaf))
		branch[2+int(newAddrNibbles[1])] = 160
		for i := 0; i < 32; i++ {
			branch[2+int(newAddrNibbles[1])+1+i] = newLeafHash[i]
		}

		// Update branch hash in extension node
		newBranchHash := common.BytesToHash(hasher.HashData(branch))
		for i := 0; i < 32; i++ {
			ext[3+i] = newBranchHash[i]
		}

		accountAddr = newAddrNibbles
		addrh = newAddrBytes

		accountProof = make([][]byte, 3)
		accountProof[0] = ext
		accountProof[1] = branch
		accountProof[2] = leaf
		accountProof1 = accountProof

		sRoot = common.BytesToHash(hasher.HashData(accountProof[0]))
		cRoot = common.BytesToHash(hasher.HashData(accountProof1[0]))
	}

	return addrh, accountAddr, accountProof, accountProof1, sRoot, cRoot
}
