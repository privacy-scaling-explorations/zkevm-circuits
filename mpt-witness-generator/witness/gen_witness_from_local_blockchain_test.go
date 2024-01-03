package witness

import (
	"fmt"
	"math/big"
	"os/exec"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/oracle"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/state"
)

func SkipIfNoGeth(t *testing.T) {
	_, err := exec.LookPath("geth")
	if err != nil {
	// TODO, fix this
	os.Setenv("NO_GETH", "1")
	if os.Getenv("NO_GETH") != "" {
		t.Skip("Skipping test that requires geth")
	}
}

func TestNonExistingAccountNilObjectInFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	// There is one branch in the state trie, but at this address there is only a nil object:
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Address: addr,
		Type:    AccountDoesNotExist,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("NonExistingAccountNilObjectInFirstLevel", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestNonExistingAccountInFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Only one element in the trie - the account with "wrong" address.
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 10
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Type:    AccountDoesNotExist,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitnessSpecial("NonExistingAccountInFirstLevel", trieModifications, statedb, 4)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestNonExistingAccountAfterFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 22
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Address: addr,
		Type:    AccountDoesNotExist,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("NonExistingAccountAfterFirstLevel", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

// Account leaf after one branch. No storage proof.
func TestAccountAfterFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Type:    BalanceChanged,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountAfterFirstLevel", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

// Account leaf in first level in C proof, placeholder leaf in S proof. No storage proof.
func TestAccountInFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Type:    NonceChanged,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitnessSpecial("AccountInFirstLevel", trieModifications, statedb, 1)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestAccountExtensionInFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xa21%d", 0)
	addr := common.HexToAddress(h)
	found := false
	for i := 0; i < 100000; i++ {
		h := fmt.Sprintf("0xa21%d", i)
		addr = common.HexToAddress(h)

		statedb.CreateAccount(addr)
		statedb.IntermediateRoot(false)

		oracle.PrefetchAccount(statedb.Db.BlockNumber, addr, nil)
		proof1, _, _, _, _, err := statedb.GetProof(addr)
		check(err)

		for j := 0; j < len(proof1)-1; j++ {
			if proof1[j][0] < 248 { // searching extension node
				found = true
			}
		}

		if found {
			break
		}
	}

	trieMod := TrieModification{
		Type:    NonceChanged,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitnessSpecial("AccountExtensionInFirstLevel", trieModifications, statedb, 5)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestAccountBranchPlaceholder(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xab%d", 0)
	addr := common.HexToAddress(h)
	// Implicitly create account such that the account from the first level will be
	// replaced by a branch.
	trieMod := TrieModification{
		Type:    NonceChanged,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountBranchPlaceholder", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestAccountBranchPlaceholderInFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xab%d", 0)
	addr := common.HexToAddress(h)
	// Implicitly create account such that the account from the first level will be
	// replaced by a branch.
	trieMod := TrieModification{
		Type:    BalanceChanged,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitnessSpecial("AccountBranchPlaceholderInFirstLevel", trieModifications, statedb, 3) // don't use the same number as in the test above

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestStorageInFirstAccountInFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     common.HexToHash("0x12"),
		Value:   common.BigToHash(big.NewInt(int64(17))),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitnessSpecial("StorageInFirstAccountInFirstLevel", trieModifications, statedb, 1)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestExtensionTwoNibblesInEvenLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xa21%d", 0)
	addr := common.HexToAddress(h)
	found := false
	for i := 0; i < 100000; i++ {
		h := fmt.Sprintf("0xa21%d", i)
		addr = common.HexToAddress(h)

		statedb.CreateAccount(addr)
		statedb.IntermediateRoot(false)

		oracle.PrefetchAccount(statedb.Db.BlockNumber, addr, nil)
		proof1, _, _, _, _, err := statedb.GetProof(addr)
		check(err)

		for j := 0; j < len(proof1)-1; j++ {
			if proof1[j][0] == 228 && proof1[j][1] == 130 && j%2 == 0 {
				found = true
			}
		}

		if found {
			break
		}
	}

	trieMod := TrieModification{
		Type:    NonceChanged,
		Nonce:   33,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountExtensionTwoNibblesInEvenLevel", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestExtensionThreeNibblesInEvenLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xa21%d", 0)
	addr := common.HexToAddress(h)
	found := false
	for i := 0; i < 100000; i++ {
		h := fmt.Sprintf("0xa21%d", i)
		addr = common.HexToAddress(h)

		statedb.CreateAccount(addr)
		statedb.IntermediateRoot(false)

		oracle.PrefetchAccount(statedb.Db.BlockNumber, addr, nil)
		proof1, _, _, _, _, err := statedb.GetProof(addr)
		check(err)

		for j := 0; j < len(proof1)-1; j++ {
			if proof1[j][0] == 228 && proof1[j][1] == 130 && j%2 == 1 {
				found = true
			}
		}

		if found {
			break
		}
	}

	trieMod := TrieModification{
		Type:    NonceChanged,
		Nonce:   33,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountExtensionThreeNibblesInEvenLevel", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestExtensionThreeNibblesInOddLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xa21%d", 0)
	addr := common.HexToAddress(h)
	found := false
	for i := 0; i < 100000; i++ {
		h := fmt.Sprintf("0xa21%d", i)
		addr = common.HexToAddress(h)

		statedb.CreateAccount(addr)
		statedb.IntermediateRoot(false)

		oracle.PrefetchAccount(statedb.Db.BlockNumber, addr, nil)
		proof1, _, _, _, _, err := statedb.GetProof(addr)
		check(err)

		for j := 0; j < len(proof1)-1; j++ {
			if proof1[j][0] == 228 && proof1[j][1] == 130 && proof1[j][2] != 0 && j%2 == 0 {
				found = true
			}
		}

		if found {
			break
		}
	}

	trieMod := TrieModification{
		Type:    NonceChanged,
		Nonce:   33,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountExtensionThreeNibblesInOddLevel", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestStorageInFirstLevelNonExisting(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	val1 := common.BigToHash(big.NewInt(int64(1)))
	statedb.SetState(addr, common.HexToHash("0x11"), val1)
	statedb.IntermediateRoot(false)

	trieMod := TrieModification{
		Type:    StorageDoesNotExist,
		Key:     common.HexToHash("0x12"),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("StorageInFirstLevelNonExisting", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func TestStorageInFirstLevelNonExistingLong(t *testing.T) {
	SkipIfNoGeth(t)
	// geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc
	oracle.NodeUrl = oracle.LocalUrl
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	val1 := common.BytesToHash(v1)
	statedb.SetState(addr, common.HexToHash("0x11"), val1)
	statedb.IntermediateRoot(false)

	trieMod := TrieModification{
		Type:    StorageDoesNotExist,
		Key:     common.HexToHash("0x12"),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("StorageInFirstLevelNonExistingLong", trieModifications, statedb)

	oracle.NodeUrl = oracle.RemoteUrl
}

func ExtNodeInserted(key1, key2, key3 common.Hash, testName string) {
	oracle.NodeUrl = oracle.LocalUrl

	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()
	statedb.CreateAccount(addr)
	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	// make the value long to have a hashed branch
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	val1 := common.BytesToHash(v1)
	statedb.SetState(addr, key1, val1)

	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	v1 = common.FromHex("0xbb")
	val := common.BytesToHash(v1)
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key3,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness(testName, trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func ExtNodeDeleted(key1, key2, key3 common.Hash, testName string) {
	oracle.NodeUrl = oracle.LocalUrl

	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()
	statedb.CreateAccount(addr)
	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	// make the value long to have a hashed branch
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaab")
	val1 := common.BytesToHash(v1)
	statedb.SetState(addr, key1, val1)
	statedb.SetState(addr, key2, val1)
	statedb.SetState(addr, key3, val1)

	statedb.IntermediateRoot(false)

	val := common.Hash{} // empty value deletes the key

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key3,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness(testName, trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func TestExtNodeInsertedBefore6After1FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 6 - means that the long (as named in the circuit) extension node has 6 nibbles.
	// After 1 - the short extension node has 1 nibble.
	// Middle 4 - the middle extension node has 4 nibbles.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x1234561000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.
	// When the nibbles are compressed into bytes, we get: [1 * 16 + 2, 3 * 16 + 4, 5 * 16 + 6, 1 * 16, 0, ..., 0].

	key2 := common.HexToHash("0x1234563000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 1 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x1234400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with the following nibbles: 1 2 3 4.
	// The branch of E1 has two nodes: the extension node E2 at position 5 (with only one nibble: 6)
	// and the leaf at position 4.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The first two keys are inserted in the trie, then we obtain the proof for the insertion of key3.
	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedBefore6After1FirstLevel")
}

func TestExtNodeDeletedBefore6After1FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 6 - means that the long (as named in the circuit) extension node has 6 nibbles.
	// After 1 - the short extension node has 1 nibble.
	// Middle 4 - the middle extension node has 4 nibbles.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x1234561000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.
	// When the nibbles are compressed into bytes, we get: [1 * 16 + 2, 3 * 16 + 4, 5 * 16 + 6, 1 * 16, 0, ..., 0].

	key2 := common.HexToHash("0x1234563000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 1 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x1234400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with the following nibbles: 1 2 3 4.
	// The branch of E1 has two nodes: the extension node E2 at position 5 (with only one nibble: 6)
	// and the leaf at position 4.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The three keys are inserted in the trie, then we obtain the proof for the deletion of key3.
	ExtNodeDeleted(key1, key2, key3, "ExtNodeDeletedBefore6After1FirstLevel")
}

func TestExtNodeInsertedBefore6After2FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 6 - means that the long (as named in the circuit) extension node has 6 nibbles.
	// After 2 - the short extension node has 2 nibbles.
	// Middle 3 - the middle extension node has 3 nibbles.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x1234561000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.
	// When the nibbles are compressed into bytes, we get: [1 * 16 + 2, 3 * 16 + 4, 5 * 16 + 6, 1 * 16, 0, ..., 0].

	key2 := common.HexToHash("0x1234563000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 1 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x1235400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with the following nibbles: 1 2 3.
	// The branch of E1 has two nodes: the extension node E2 at position 4 (with two nibbles: 5 6)
	// and the leaf at position 5.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The first two keys are inserted in the trie, then we obtain the proof for the insertion of key3.
	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedBefore6After2FirstLevel")
}

func TestExtNodeInsertedBefore6After4FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 6 - means that the long (as named in the circuit) extension node has 6 nibbles.
	// After 4 - the short extension node has 4 nibbles.
	// Middle 1 - the middle extension node has 1 nibble.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x1234561000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.
	// When the nibbles are compressed into bytes, we get: [1 * 16 + 2, 3 * 16 + 4, 5 * 16 + 6, 1 * 16, 0, ..., 0].

	key2 := common.HexToHash("0x1234563000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 1 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x1635400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with one nibble: 1.
	// The branch of E1 has two nodes: the extension node E2 at position 2 (with four nibbles: 3 4 5 6)
	// and the leaf at position 6.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The first two keys are inserted in the trie, then we obtain the proof for the insertion of key3.
	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedBefore6After4FirstLevel")
}

func TestExtNodeInsertedBefore5After3FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 5 - means that the long (as named in the circuit) extension node has 5 nibbles.
	// After 3 - the short extension node has 3 nibbles.
	// Middle 1 - the middle extension node has 1 nibble.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.

	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x2635400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with one nibble: 2.
	// The branch of E1 has two nodes: the extension node E2 at position 3 (with three nibbles: 4 5 6)
	// and the leaf at position 6.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The first two keys are inserted in the trie, then we obtain the proof for the insertion of key3.
	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedBefore5After3FirstLevel")
}

func TestExtNodeInsertedBefore5After2FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 5 - means that the long (as named in the circuit) extension node has 5 nibbles.
	// After 2 - the short extension node has 2 nibbles.
	// Middle 2 - the middle extension node has 2 nibbles.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.

	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x2335400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with two nibbles: 2 3.
	// The branch of E1 has two nodes: the extension node E2 at position 4 (with two nibbles: 5 6)
	// and the leaf at position 3.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The first two keys are inserted in the trie, then we obtain the proof for the insertion of key3.
	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedBefore5After2FirstLevel")
}

func TestExtNodeInsertedBefore5After1FirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 5 - means that the long (as named in the circuit) extension node has 5 nibbles.
	// After 1 - the short extension node has 1 nibble.
	// Middle 3 - the middle extension node has 3 nibbles.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.

	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x2343540000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with three nibbles: 2 3 4.
	// The branch of E1 has two nodes: the extension node E2 at position 5 (with one nibble: 6)
	// and the leaf at position 3.
	// The branch of E2 has two leaves - at position 1 and 3.

	// The first two keys are inserted in the trie, then we obtain the proof for the insertion of key3.
	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedBefore5After1FirstLevel")
}

func TestExtNodeInsertedBefore4After1(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 4 - means that the long (as named in the circuit) extension node has 4 nibbles.
	// After 1 - the short extension node has 1 nibble.
	// Middle 2 - the middle extension node has 2 nibbles.

	oracle.NodeUrl = oracle.LocalUrl

	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	statedb.CreateAccount(addr)

	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	val0 := common.BigToHash(big.NewInt(int64(1)))
	key0 := common.HexToHash("0x1000000000000000000000000000000000000000000000000000000000000000")
	statedb.SetState(addr, key0, val0)

	key00 := common.HexToHash("0x0000000000000000000000000000000000000000000000000000000000000000")
	statedb.SetState(addr, key00, val0)
	// After insertion of key0 and key00, we have a branch B with two leaves - at position 1 and 0.

	key1 := common.HexToHash("0x1234561000000000000000000000000000000000000000000000000000000000")

	// make the value long to have a hashed branch
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	val1 := common.BytesToHash(v1)
	statedb.SetState(addr, key1, val1)
	// After insertion of key1, we have a branch B with a leaf at position 0 and a branch B1 at position 1.
	// Branch B1 has two leaves - at position 0 and 2.

	key2 := common.HexToHash("0x1234563000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have a branch B1 with two nodes - a leaf at position 0 and an extension
	// node E (with nibbles 3 4 5 6) at position 2.

	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	key3 := common.HexToHash("0x1234400000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with two nibbles: 3 4.
	// The branch of E1 has two nodes: the extension node E2 at position 5 (with one nibble: 6)
	// and the leaf at position 4.
	// The branch of E2 has two leaves - at position 1 and 3.

	v1 = common.FromHex("0xbb")
	val := common.BytesToHash(v1)
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key3,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtNodeInsertedBefore4After1", trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func TestExtNodeDeletedBefore4After1(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 4 - means that the long (as named in the circuit) extension node has 4 nibbles.
	// After 1 - the short extension node has 1 nibble.
	// Middle 2 - the middle extension node has 2 nibbles.

	// This is the reverse operation of the case in TestExtNodeInsertedBefore4After1.

	oracle.NodeUrl = oracle.LocalUrl

	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	statedb.CreateAccount(addr)

	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	val0 := common.BigToHash(big.NewInt(int64(1)))
	key0 := common.HexToHash("0x1000000000000000000000000000000000000000000000000000000000000000")
	statedb.SetState(addr, key0, val0)

	key00 := common.HexToHash("0x0000000000000000000000000000000000000000000000000000000000000000")
	statedb.SetState(addr, key00, val0)
	// After insertion of key0 and key00, we have a branch B with two leaves - at position 1 and 0.

	key1 := common.HexToHash("0x1234561000000000000000000000000000000000000000000000000000000000")
	// After insertion of key1, we have a branch B with a leaf at position 0 and a branch B1 at position 1.
	// Branch B1 has two leaves - at position 0 and 2.

	// make the value long to have a hashed branch
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	val1 := common.BytesToHash(v1)
	statedb.SetState(addr, key1, val1)

	key2 := common.HexToHash("0x1234563000000000000000000000000000000000000000000000000000000000")
	statedb.SetState(addr, key2, val1)
	// After inserting key2, we have a branch B1 with two nodes - a leaf at position 0 and an extension
	// node E (with nibbles 3 4 5 6) at position 2.

	key3 := common.HexToHash("0x1234400000000000000000000000000000000000000000000000000000000000")
	statedb.SetState(addr, key3, val1)
	// After inserting key3, we have an extension node E1 with two nibbles: 3 4.
	// The branch of E1 has two nodes: the extension node E2 at position 5 (with one nibble: 6)
	// and the leaf at position 4.
	// The branch of E2 has two leaves - at position 1 and 3.

	statedb.IntermediateRoot(false)

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key3,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtNodeDeletedBefore4After1", trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func TestExtNodeInNewBranchFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 5 - means that the long (as named in the circuit) extension node has 5 nibbles.
	// After 1 - the short extension node has 4 nibbles.
	// Middle - the middle node is a branch.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.

	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x6354000000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have a branch B with an extension node E1 at position 2 (with nibbles 3 4 5 6)
	// and a leaf at position 6.

	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedInNewBranchFirstLevel")
}

func TestExtNodeDeletedBranchDeletedFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// This is the reverse operation of the case in TestExtNodeInNewBranchFirstLevel.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	key3 := common.HexToHash("0x6354000000000000000000000000000000000000000000000000000000000000")

	ExtNodeDeleted(key1, key2, key3, "ExtNodeDeletedBranchDeletedFirstLevel")
}

func TestExtNodeInsertedExtShortIsBranchFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// Before 5 - means that the long (as named in the circuit) extension node has 5 nibbles.
	// After - the short node is a branch.
	// Middle 3 - the middle extension node has 3 nibbles.

	// The trie is empty before we add key1, key2, key3.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	// After inserting key1, there is only one leaf in the trie.

	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	// After inserting key2, we have an extension node E in the trie with the following nibbles: 2 3 4 5 6.
	// The branch of the extension node has two leaves - key1 at position 1 and key2 at position 3.

	key3 := common.HexToHash("0x2345100000000000000000000000000000000000000000000000000000000000")
	// After inserting key3, we have an extension node E1 with nibbles: 2 3 4 5.
	// The branch of E1 has two nodes: the branch at position 6 and the leaf at position 1.

	ExtNodeInserted(key1, key2, key3, "ExtNodeInsertedExtShortIsBranchFirstLevel")
}

func TestExtNodeDeletedExtShortIsBranchFirstLevel(t *testing.T) {
	SkipIfNoGeth(t)
	// This is the reverse operation of the case in TestExtNodeInsertedExtShortIsBranchFirstLevel.
	key1 := common.HexToHash("0x2345610000000000000000000000000000000000000000000000000000000000")
	key2 := common.HexToHash("0x2345630000000000000000000000000000000000000000000000000000000000")
	key3 := common.HexToHash("0x2345100000000000000000000000000000000000000000000000000000000000")

	ExtNodeDeleted(key1, key2, key3, "ExtNodeDeletedExtShortIsBranchFirstLevel")
}
