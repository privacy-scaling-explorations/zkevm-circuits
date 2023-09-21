package witness

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/oracle"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/state"
)

func TestUpdateOneLevel(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// We have a branch with children at position 3 and 11.

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}

	// This key is turned into odd length (see hexToCompact in encoding.go to see
	// odd and even length are handled differently)
	v := common.BigToHash(big.NewInt(int64(17)))
	addr := common.HexToAddress("0xaaaccf12580138bc2bbceeeaa111df4e42ab81ff")

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     ks[0],
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateOneLevel", ks[:], values, []common.Address{addr, addr}, trieModifications)
}

func TestUpdateOneLevel1(t *testing.T) {
	addr := common.HexToAddress("0x50efbf12580138bc263c95757826df4e24eb81c9")
	// This address is turned into odd length (see hexToCompact in encoding.go to see
	// odd and even length are handled differently)
	ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}
	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     ks[1],
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateOneLevel1", ks[:], values, []common.Address{addr, addr}, trieModifications)
}

func TestUpdateOneLevelBigVal(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// We have a branch with children at position 3 and 11.

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}

	// ks[0] key is turned into odd length (see hexToCompact in encoding.go to see
	// odd and even length are handled differently)
	// big value so that RLP is longer than 55 bytes
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	addr := common.HexToAddress("0xaaaccf12580138bc2bbceeeaa826df4e42ab81ff")

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     ks[0],
		Value:   v2,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateOneLevelBigVal", ks[:], values, []common.Address{addr, addr}, trieModifications)
}

func TestUpdateTwoLevels(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12"), common.HexToHash("0x21")} // this has three levels
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// First we have a branch with children at position 3 and 11.
	// The third storage change happens at key:
	// [3,10,6,3,5,7,...
	// That means leaf at position 3 turns into branch with children at position 1 and 10.
	// ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}

	// This key is turned into even length (see hexToCompact in encoding.go to see
	// odd and even length are handled differently)
	v := common.BigToHash(big.NewInt(int64(17)))
	addr := common.HexToAddress("0xaaaccf12580138bc2bbc957aa826df4e42ab81ff")

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     ks[0],
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateTwoLevels", ks[:], values, []common.Address{addr, addr, addr}, trieModifications)
}

func TestUpdateTwoLevelsBigVal(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12"), common.HexToHash("0x21")} // this has three levels
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// First we have a branch with children at position 3 and 11.
	// The third storage change happens at key:
	// [3,10,6,3,5,7,...
	// That means leaf at position 3 turns into branch with children at position 1 and 10.
	// ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}

	// This key is turned into even length (see hexToCompact in encoding.go to see
	// odd and even length are handled differently)
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	addr := common.HexToAddress("0xaaaccf12580138bc2bbc957aa826df4e42ab81ff")

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     ks[0],
		Value:   v2,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateTwoLevelsBigVal", ks[:], values, []common.Address{addr, addr, addr}, trieModifications)
}

func TestUpdateThreeLevels(t *testing.T) {
	ks := [...]common.Hash{
		common.HexToHash("0x11"),
		common.HexToHash("0x12"),
		common.HexToHash("0x21"),
		common.HexToHash("0x31"),
		common.HexToHash("0x32"),
		common.HexToHash("0x33"),
		common.HexToHash("0x34"),
		common.HexToHash("0x35"),
		common.HexToHash("0x36"),
		common.HexToHash("0x37"),
		common.HexToHash("0x38"), //
		common.HexToHash("0x39"),
		common.HexToHash("0x40"),
		common.HexToHash("0x41"),
		common.HexToHash("0x42"),
		common.HexToHash("0x43"),
		common.HexToHash("0x44"),
		common.HexToHash("0x45"),
		common.HexToHash("0x46"),
	}
	// ks[10] = 0x38 is at position 3 in root.Children[3].Children[8]
	// nibbles
	// [9,5,12,5,13,12,14,10,13,14,9,6,0,3,4,7,9,11,1,7,7,11,6,8,9,5,9,0,4,9,4,8,5,13,15,8,10,10,9,7,11,3,9,15,3,5,3,3,0,3,9,10,15,5,15,4,5,6,1,9,9,16]
	// terminator flag 16 (last byte) is removed, then it remains len 61 (these are nibbles):
	// [9,5,12,5,13,12,14,10,13,14,9,6,0,3,4,7,9,11,1,7,7,11,6,8,9,5,9,0,4,9,4,8,5,13,15,8,10,10,9,7,11,3,9,15,3,5,3,3,0,3,9,10,15,5,15,4,5,6,1,9,9]

	// buf (31 len):
	// this is key stored in leaf:
	// [57,92,93,206,173,233,96,52,121,177,119,182,137,89,4,148,133,223,138,169,123,57,243,83,48,57,175,95,69,97,153]

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0xaaaccf12580138bc263c95757826df4e42ab81ff")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	v := common.BigToHash(big.NewInt(int64(17)))

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     ks[10],
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateThreeLevels", ks[:], values, addresses, trieModifications)
}

func TestFromNilToValue(t *testing.T) {
	ks := [...]common.Hash{
		common.HexToHash("0x11"),
		common.HexToHash("0x12"),
		common.HexToHash("0x21"),
		common.HexToHash("0x31"),
		common.HexToHash("0x32"),
		common.HexToHash("0x33"),
		common.HexToHash("0x34"),
		common.HexToHash("0x35"),
		common.HexToHash("0x36"),
		common.HexToHash("0x37"),
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x50efbf12580138bc263c95757826df4e42ab81ff")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	// This test is similar as above, but the key that is being modified has not been used yet.

	toBeModified := common.HexToHash("0x38")
	v := common.BigToHash(big.NewInt(int64(17)))

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("FromNilToValue", ks[:], values, addresses, trieModifications)
}

func TestDelete(t *testing.T) {
	ks := [...]common.Hash{
		common.HexToHash("0xaaaabbbbabab"),
		common.HexToHash("0xbaaabbbbabab"),
		common.HexToHash("0xcaaabbbbabab"),
		common.HexToHash("0xdaaabbbbabab"),
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x50efbf12580138bc263c95757826df4e24eb81ff")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0xdaaabbbbabab")
	val := common.Hash{} // empty value deletes the key

	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("Delete", ks[:], values, addresses, trieModifications)
}

func TestUpdateOneLevelEvenAddress(t *testing.T) {
	addr := common.HexToAddress("0x25efbf12580138bc263c95757826df4e24eb81c9")
	// This address is turned into even length (see hexToCompact in encoding.go to see
	// odd and even length are handled differently)
	ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}
	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	// This is a storage slot that will be modified (the list will come from bus-mapping):
	toBeModified := ks[1]
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("UpdateOneLevelEvenAddress", ks[:], values, addresses, trieModifications)
}

func TestAddBranch(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12")}
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// First we have a branch with children at position 3 and 11.
	// ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75acef12a01883c2b3fc57957826df4e24e8baaa")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	// This key is not in the trie yet, its nibbles:
	// [3,10,6,3,5,7,...
	// That means leaf at position 3 turns into branch with children at position 1 and 10.
	toBeModified := common.HexToHash("0x21")
	v := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("AddBranch", ks[:], values, addresses, trieModifications)
}

func TestAddBranchLong(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12")}
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// First we have a branch with children at position 3 and 11.
	// ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}

	var values []common.Hash
	// big value so that RLP will be longer than 55 bytes for the neighbouring node
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	for i := 0; i < len(ks); i++ {
		values = append(values, v2)
	}
	addr := common.HexToAddress("0x75acef12a01883c2b3fc57957826df4e24e8b19c")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	// This key is not in the trie yet, its nibbles:
	// [3,10,6,3,5,7,...
	// That means leaf at position 3 turns into branch with children at position 1 and 10.
	toBeModified := common.HexToHash("0x21")
	v := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("AddBranchLong", ks[:], values, addresses, trieModifications)
}

func TestDeleteBranch(t *testing.T) {
	h := common.HexToHash("0x11dd2277aa")

	ks := [...]common.Hash{
		common.HexToHash("0xaa"),
		common.HexToHash("0xabcc"),
		common.HexToHash("0xffdd"),
		common.HexToHash("0x11dd"),
		common.HexToHash("0x11dd22"),
		common.HexToHash("0x11dd2233"),
		common.HexToHash("0x11dd2255"),
		common.HexToHash("0x11dd2277"),
		h, // this leaf turns into a branch
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75acef12a0188c32b36c57957826df4e24e8b19c")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := h
	v := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("DeleteBranch", ks[:], values, addresses, trieModifications)
}

func TestDeleteBranchLong(t *testing.T) {
	h := common.HexToHash("0x11dd2277aa")

	ks := [...]common.Hash{
		common.HexToHash("0xaa"),
		common.HexToHash("0xabcc"),
		common.HexToHash("0xffdd"),
		common.HexToHash("0x11dd"),
		common.HexToHash("0x11dd22"),
		common.HexToHash("0x11dd2233"),
		common.HexToHash("0x11dd2255"),
		common.HexToHash("0x11dd2277"),
		h, // this leaf turns into a branch
	}

	var values []common.Hash
	// big value so that RLP will be longer than 55 bytes for the neighbouring node
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	for i := 0; i < len(ks); i++ {
		values = append(values, v2)
	}
	addr := common.HexToAddress("0x75acef12a0188c32b36c57957826df4e24e8b19c")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := h
	v := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("DeleteBranchLong", ks[:], values, addresses, trieModifications)
}

func TestAddBranchTwoLevels(t *testing.T) {
	// Test for case when branch is added in the second level. So, instead of having only
	// branch1 with some nodes and then one of this nodes is replaced with a branch (that's
	// the case of TestAddBranch), we have here branch1 and then inside it another
	// branch: branch2. Inside brach2 we have a node which gets replaced by a branch.
	// This is to test cases when the key contains odd number of nibbles as well as
	// even number of nibbles.

	a := 1
	b := 1
	h := fmt.Sprintf("0xaa%d%d", a, b)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 33; i++ {
		// just some values to get the added branch in second level (found out trying different values)
		if i%2 == 0 {
			a += 1
		} else {
			b += 1
		}
		if a == 4 && b == 3 {
			continue
		}
		h := fmt.Sprintf("0xaa%d%d", a, b)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef12a0188c32b36c57957826df4e24e8b19c")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0xaa43")
	v := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("AddBranchTwoLevels", ks[:], values, addresses, trieModifications)
}

func TestAddBranchTwoLevelsLong(t *testing.T) {
	a := 1
	b := 1
	h := fmt.Sprintf("0xaa%d%d", a, b)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 33; i++ {
		// just some values to get the added branch in second level (found out trying different values)
		if i%2 == 0 {
			a += 1
		} else {
			b += 1
		}
		if a == 4 && b == 3 {
			continue
		}
		h := fmt.Sprintf("0xaa%d%d", a, b)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	for i := 0; i < len(ks); i++ {
		values = append(values, v2)
	}
	addr := common.HexToAddress("0x75fbef1250188c32b63c57957826df4e24e8b19c")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0xaa43")
	v := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("AddBranchTwoLevelsLong", ks[:], values, addresses, trieModifications)
}

func TestDeleteBranchTwoLevels(t *testing.T) {
	a := 1
	b := 1
	h := fmt.Sprintf("0xaa%d%d", a, b)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 33; i++ {
		// just some values to get the added branch in second level (found out trying different values)
		if i%2 == 0 {
			a += 1
		} else {
			b += 1
		}
		h := fmt.Sprintf("0xaa%d%d", a, b)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef1250188c32b63c57957826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0xaa43")
	v := common.Hash{}
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("DeleteBranchTwoLevels", ks[:], values, addresses, trieModifications)
}

func TestDeleteBranchTwoLevelsLong(t *testing.T) {
	a := 1
	b := 1
	h := fmt.Sprintf("0xaa%d%d", a, b)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 33; i++ {
		// just some values to get the added branch in second level (found out trying different values)
		if i%2 == 0 {
			a += 1
		} else {
			b += 1
		}
		h := fmt.Sprintf("0xaa%d%d", a, b)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	for i := 0; i < len(ks); i++ {
		values = append(values, v2)
	}
	addr := common.HexToAddress("0x75fbef21508183c2b63c57957826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0xaa43")
	v := common.Hash{}
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   v,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("DeleteBranchTwoLevelsLong", ks[:], values, addresses, trieModifications)
}

func TestExtensionOneKeyByteSel1(t *testing.T) {
	ks := [...]common.Hash{
		common.HexToHash("0x11"),
		common.HexToHash("0x12"),
		common.HexToHash("0x21"),
		common.HexToHash("0x31"),
		common.HexToHash("0x32"),
		common.HexToHash("0x33"),
		common.HexToHash("0x34"),
		common.HexToHash("0x35"),
		common.HexToHash("0x36"),
		common.HexToHash("0x37"),
		common.HexToHash("0x38"), //
		common.HexToHash("0x39"),
		common.HexToHash("0x40"),
		common.HexToHash("0x42"),
		common.HexToHash("0x43"),
		common.HexToHash("0x44"),
		common.HexToHash("0x45"),
		common.HexToHash("0x46"),
		common.HexToHash("0x47"),
		common.HexToHash("0x48"),
		common.HexToHash("0x50"),
		common.HexToHash("0x51"),
		common.HexToHash("0x52"),
		common.HexToHash("0x53"),
		common.HexToHash("0x54"),
		common.HexToHash("0x55"),
		common.HexToHash("0x56"),

		common.HexToHash("0x61"), // extension
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef21508183c2b63c57957826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := ks[len(ks)-1]
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionOneKeyByteSel1", ks[:], values, addresses, trieModifications)
}

func TestExtensionAddedOneKeyByteSel1(t *testing.T) {
	a := 1
	b := 1
	h := fmt.Sprintf("0x%d%d", a, b)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 33; i++ {
		// just some values to get the added branch in second level (found out trying different values)
		if i%2 == 0 {
			a += 1
		} else {
			b += 1
		}
		h := fmt.Sprintf("0x%d%d", a, b)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x50efbf12580138bc263c95757826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0x1818")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionAddedOneKeyByteSel1", ks[:], values, addresses, trieModifications)
}

func TestExtensionDeletedOneKeyByteSel1(t *testing.T) {
	a := 1
	b := 1
	h := fmt.Sprintf("0x%d%d", a, b)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 33; i++ {
		// just some values to get the added branch in second level (found out trying different values)
		if i%2 == 0 {
			a += 1
		} else {
			b += 1
		}
		h := fmt.Sprintf("0x%d%d", a, b)
		ks = append(ks, common.HexToHash(h))
	}
	toBeModified := common.HexToHash("0x1818")
	ks = append(ks, toBeModified)

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x50efbf12580138bc263c95757826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionDeletedOneKeyByteSel1", ks[:], values, addresses, trieModifications)
}

func TestExtensionOneKeyByteSel2(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0xca%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 876; i++ {
		a += 1
		h := fmt.Sprintf("0xca%d", a)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0xca644")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionOneKeyByteSel2", ks[:], values, addresses, trieModifications)
}

func TestExtensionAddedOneKeyByteSel2(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0xca%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	toBeModifiedStr := "0xca644"
	toBeModified := common.HexToHash(toBeModifiedStr)
	for i := 0; i < 876; i++ {
		a += 1
		h := fmt.Sprintf("0xca%d", a)
		if h == toBeModifiedStr {
			continue
		}
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionAddedOneKeyByteSel2", ks[:], values, addresses, trieModifications)
}

func TestExtensionDeletedOneKeyByteSel2(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0xca%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	toBeModifiedStr := "0xca644"
	toBeModified := common.HexToHash(toBeModifiedStr)
	for i := 0; i < 876; i++ {
		a += 1
		h := fmt.Sprintf("0xca%d", a)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionDeletedOneKeyByteSel2", ks[:], values, addresses, trieModifications)
}

func TestExtensionTwoKeyBytesSel1(t *testing.T) {
	// Extension node which has key longer than 1 (2 in this test). This is needed because RLP takes
	// different positions.
	// Key length > 1 (130 means there are two bytes for key; 160 means there are 32 hash values after it):
	// [228 130 0 149 160 ...
	// Key length = 1 (no byte specifying the length of key):
	// [226 16 160 ...
	a := 0
	h := fmt.Sprintf("0x%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 176; i++ {
		// just some values to get the extension with key length > 1 (found out trying different values)
		a += 1
		h := fmt.Sprintf("0x%d", a)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef21508183c2b63c59757826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0x172")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionTwoKeyBytesSel1", ks[:], values, addresses, trieModifications)
}

func TestExtensionAddedTwoKeyBytesSel1(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0x%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	toBeModifiedStr := "0x172"
	toBeModified := common.HexToHash(toBeModifiedStr)
	for i := 0; i < 176; i++ {
		// just some values to get the extension with key length > 1 (found out trying different values)
		a += 1
		h := fmt.Sprintf("0x%d", a)
		if h == toBeModifiedStr {
			continue
		}
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef21508183c2b63c59757826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionAddedTwoKeyBytesSel1", ks[:], values, addresses, trieModifications)
}

func TestExtensionDeletedTwoKeyBytesSel1(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0x%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	toBeModifiedStr := "0x172"
	toBeModified := common.HexToHash(toBeModifiedStr)
	for i := 0; i < 176; i++ {
		// just some values to get the extension with key length > 1 (found out trying different values)
		a += 1
		h := fmt.Sprintf("0x%d", a)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef21508183c2b63c59757826df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionDeletedTwoKeyBytesSel1", ks[:], values, addresses, trieModifications)
}

func TestExtensionTwoKeyBytesSel2(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0x2ea%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	for i := 0; i < 876; i++ {
		a += 1
		h := fmt.Sprintf("0x2ea%d", a)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0x2ea772")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionTwoKeyBytesSel2", ks[:], values, addresses, trieModifications)
}

func TestExtensionAddedTwoKeyBytesSel2(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0x2ea%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	toBeModifiedStr := "0x2ea772"
	toBeModified := common.HexToHash(toBeModifiedStr)
	for i := 0; i < 876; i++ {
		a += 1
		h := fmt.Sprintf("0x2ea%d", a)
		if h == toBeModifiedStr {
			continue
		}
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionAddedTwoKeyBytesSel2", ks[:], values, addresses, trieModifications)
}

func TestExtensionDeletedTwoKeyBytesSel2(t *testing.T) {
	a := 0
	h := fmt.Sprintf("0x2ea%d", a)
	ks := []common.Hash{common.HexToHash(h)}
	toBeModifiedStr := "0x2ea772"
	toBeModified := common.HexToHash(toBeModifiedStr)
	for i := 0; i < 876; i++ {
		a += 1
		h := fmt.Sprintf("0x2ea%d", a)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionDeletedTwoKeyBytesSel2", ks[:], values, addresses, trieModifications)
}

func TestExtensionInFirstStorageLevel(t *testing.T) {
	ks := []common.Hash{common.HexToHash("0x12")}

	for i := 0; i < 10; i++ {
		h := fmt.Sprintf("0x%d", i)
		ks = append(ks, common.HexToHash(h))
	}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75fbef2150818c32b36c57957226df4e24eb81c9")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	toBeModified := common.HexToHash("0x1")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("ExtensionInFirstStorageLevel", ks[:], values, addresses, trieModifications)
}

func TestExtensionInFirstStorageLevelOneKeyByte(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	key1 := common.HexToHash("0x12")
	val1 := common.BigToHash(big.NewInt(int64(1)))

	statedb.SetState(addr, key1, val1)

	h := fmt.Sprintf("0x%d", 1)
	key2 := common.HexToHash(h)
	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	toBeModified := common.HexToHash("0x1")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionInFirstStorageLevelOneKeyByte", trieModifications, statedb)
}

func TestExtensionAddedInFirstStorageLevelOneKeyByte(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	key1 := common.HexToHash("0x12")
	val1 := common.BigToHash(big.NewInt(int64(1)))

	statedb.SetState(addr, key1, val1)

	toBeModified := common.HexToHash("0x1")
	// statedb.SetState(addr, toBeModified, val1)
	statedb.IntermediateRoot(false)
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionAddedInFirstStorageLevelOneKeyByte", trieModifications, statedb)
}

func TestExtensionInFirstStorageLevelTwoKeyBytes(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	key1 := common.HexToHash("0x12")
	val1 := common.BigToHash(big.NewInt(int64(1)))

	statedb.SetState(addr, key1, val1)

	toBeModified := common.HexToHash("0xa617")
	statedb.SetState(addr, toBeModified, val1)
	statedb.IntermediateRoot(false)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionInFirstStorageLevelTwoKeyBytes", trieModifications, statedb)
}

func TestExtensionAddedInFirstStorageLevelTwoKeyBytes(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	key1 := common.HexToHash("0x12")
	val1 := common.BigToHash(big.NewInt(int64(1)))

	statedb.SetState(addr, key1, val1)

	toBeModified := common.HexToHash("0xa617")
	// statedb.SetState(addr, toBeModified, val1)
	statedb.IntermediateRoot(false)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionAddedInFirstStorageLevelTwoKeyBytes", trieModifications, statedb)
}

func TestExtensionThreeKeyBytesSel2(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50feb1f2580138bc623c97557286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	for i := 0; i < 14; i++ {
		h := fmt.Sprintf("0x%d", i)
		key2 := common.HexToHash(h)
		val1 := common.BigToHash(big.NewInt(int64(1)))
		statedb.SetState(addr, key2, val1)
	}

	toBeModified := common.HexToHash("0x13234")
	val1 := common.BigToHash(big.NewInt(int64(1)))
	statedb.SetState(addr, toBeModified, val1)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionThreeKeyBytesSel2", trieModifications, statedb)
}

func TestExtensionAddedThreeKeyBytesSel2(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50feb1f2580138bc623c97557286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	for i := 0; i < 14; i++ {
		h := fmt.Sprintf("0x%d", i)
		key2 := common.HexToHash(h)
		val1 := common.BigToHash(big.NewInt(int64(1)))
		statedb.SetState(addr, key2, val1)
	}

	toBeModified := common.HexToHash("0x13234")

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionAddedThreeKeyBytesSel2", trieModifications, statedb)
}

func TestExtensionDeletedThreeKeyBytesSel2(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50feb1f2580138bc623c97557286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	for i := 0; i < 14; i++ {
		h := fmt.Sprintf("0x%d", i)
		key2 := common.HexToHash(h)
		val1 := common.BigToHash(big.NewInt(int64(1)))
		statedb.SetState(addr, key2, val1)
	}

	toBeModified := common.HexToHash("0x13234")
	val1 := common.BigToHash(big.NewInt(int64(1)))
	statedb.SetState(addr, toBeModified, val1)

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionDeletedThreeKeyBytesSel2", trieModifications, statedb)
}

func TestExtensionThreeKeyBytes(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50fbe1f25aa0843b623c97557286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	for i := 0; i < 140; i++ {
		h := fmt.Sprintf("0x%d", i)
		key2 := common.HexToHash(h)
		val1 := common.BigToHash(big.NewInt(int64(1)))
		statedb.SetState(addr, key2, val1)
	}

	// Let's get a key which makes extension node at the first level.
	// (set the breakpoint in trie.go, line 313)
	for i := 0; i < 1000; i++ {
		h := fmt.Sprintf("0x2111d%d", i)
		key2 := common.HexToHash(h)
		val1 := common.BigToHash(big.NewInt(int64(1)))
		statedb.SetState(addr, key2, val1)
		statedb.IntermediateRoot(false)

		// v := common.Hash{} // empty value deletes the key
		// statedb.SetState(addr, key2, v)
	}

	toBeModified := common.HexToHash("0x333")
	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     toBeModified,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ExtensionThreeKeyBytes", trieModifications, statedb)
}

func TestOnlyLeafInStorageProof(t *testing.T) {
	blockNum := 14209217
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	statedb.DisableLoadingRemoteAccounts()

	h := fmt.Sprintf("0x%d", 0)
	addr := common.HexToAddress(h)
	// statedb.IntermediateRoot(false)
	statedb.CreateAccount(addr)

	accountProof, _, _, _, err := statedb.GetProof(addr)
	fmt.Println(len(accountProof))
	check(err)

	h = fmt.Sprintf("0x2111d%d", 0)
	key2 := common.HexToHash(h)
	val1 := common.BigToHash(big.NewInt(int64(1)))
	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	// storageProof, _, _, _, err := statedb.GetStorageProof(addr, key2)
	// check(err)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key2,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("OnlyLeafInStorageProof", trieModifications, statedb)
}

func TestStorageLeafInFirstLevelAfterPlaceholder(t *testing.T) {
	blockNum := 14209217
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	statedb.DisableLoadingRemoteAccounts()

	h := fmt.Sprintf("0x%d", 0)
	addr := common.HexToAddress(h)
	// statedb.IntermediateRoot(false)
	statedb.CreateAccount(addr)

	accountProof, _, _, _, err := statedb.GetProof(addr)
	fmt.Println(len(accountProof))
	check(err)

	h1 := fmt.Sprintf("0x2111d%d", 0)
	key1 := common.HexToHash(h1)
	val1 := common.BigToHash(big.NewInt(int64(1)))
	statedb.SetState(addr, key1, val1)
	statedb.IntermediateRoot(false)

	// storageProof, _, _, _, err := statedb.GetStorageProof(addr, key2)
	// check(err)

	h2 := fmt.Sprintf("0x2111%d", 0)
	key2 := common.HexToHash(h2)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key2,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("StorageLeafInFirstLevelAfterPlaceholder", trieModifications, statedb)
}

func TestLeafAddedToEmptyTrie(t *testing.T) {
	blockNum := 14209217
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	statedb.DisableLoadingRemoteAccounts()

	h := fmt.Sprintf("0x%d", 0)
	addr := common.HexToAddress(h)
	// statedb.IntermediateRoot(false)
	statedb.CreateAccount(addr)

	accountProof, _, _, _, err := statedb.GetProof(addr)
	fmt.Println(len(accountProof))
	check(err)

	// emptyTrieHash := statedb.StorageTrie(addr).Hash()
	// fmt.Println(emptyTrieHash.Bytes())

	h = fmt.Sprintf("0x2111d%d", 0)
	key2 := common.HexToHash(h)
	// val1 := common.BigToHash(big.NewInt(int64(1)))
	// statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	// storageProof, _, _, _, err := statedb.GetStorageProof(addr, key2)
	// check(err)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key2,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("LeafAddedToEmptyTrie", trieModifications, statedb)
}

func TestDeleteToEmptyTrie(t *testing.T) {
	blockNum := 14209217
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	statedb.DisableLoadingRemoteAccounts()

	h := fmt.Sprintf("0x%d", 0)
	addr := common.HexToAddress(h)
	// statedb.IntermediateRoot(false)
	statedb.CreateAccount(addr)

	accountProof, _, _, _, err := statedb.GetProof(addr)
	fmt.Println(len(accountProof))
	check(err)

	h = fmt.Sprintf("0x2111d%d", 0)
	key2 := common.HexToHash(h)
	val1 := common.BigToHash(big.NewInt(int64(1)))
	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	// storageProof, _, _, _, err := statedb.GetStorageProof(addr, key2)
	// check(err)

	val := common.Hash{} // empty value deletes the key
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key2,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("DeleteToEmptyTrie", trieModifications, statedb)
}

func TestUpdateTwoModifications(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}
	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0xaaaccf12580138bc2bbceeeaa111df4e42ab81ff")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	v1 := common.BigToHash(big.NewInt(int64(17)))
	v2 := common.BigToHash(big.NewInt(int64(17)))

	trieMod1 := TrieModification{
		Type:    StorageChanged,
		Key:     ks[0],
		Value:   v1,
		Address: addr,
	}
	trieMod2 := TrieModification{
		Type:    StorageChanged,
		Key:     ks[1],
		Value:   v2,
		Address: addr,
	}

	trieModifications := []TrieModification{trieMod1, trieMod2}

	updateStateAndPrepareWitness("UpdateTwoModifications", ks[:], values, addresses, trieModifications)
}

func TestNonceModCShort(t *testing.T) {
	blockNum := 14766377
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x68D5a6E78BD8734B7d190cbD98549B72bFa0800B")

	trieMod := TrieModification{
		Type:    NonceChanged,
		Nonce:   33,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("NonceModCShort", trieModifications, statedb)
}

func TestNonceModCLong(t *testing.T) {
	blockNum := 14766377
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x68D5a6E78BD8734B7d190cbD98549B72bFa0800B")

	trieMod := TrieModification{
		Type:    NonceChanged,
		Nonce:   142, // for long needs to be >= 128
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("NonceModCLong", trieModifications, statedb)
}

func TestBalanceModCShort(t *testing.T) {
	blockNum := 14766377
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x68D5a6E78BD8734B7d190cbD98549B72bFa0800B")

	trieMod := TrieModification{
		Type:    BalanceChanged,
		Balance: big.NewInt(98),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("BalanceModCShort", trieModifications, statedb)
}

func TestBalanceModCLong(t *testing.T) {
	blockNum := 14766377
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x68D5a6E78BD8734B7d190cbD98549B72bFa0800B")

	trieMod := TrieModification{
		Type:    BalanceChanged,
		Balance: big.NewInt(439),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("BalanceModCLong", trieModifications, statedb)
}

func TestAddAccount(t *testing.T) {
	blockNum := 1
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	addr := common.HexToAddress("0xaaaccf12580138bc2bbceeeaa111df4e42ab81ab")
	statedb.IntermediateRoot(false)

	trieMod := TrieModification{
		Address: addr,
		Type:    AccountCreate,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AddAccount", trieModifications, statedb)
}

func TestDeleteAccount(t *testing.T) {
	blockNum := 1
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	addr := common.HexToAddress("0xaaaccf12580138bc2bbceeeaa111df4e42ab81ab")
	statedb.CreateAccount(addr)
	statedb.IntermediateRoot(false)

	trieMod := TrieModification{
		Address: addr,
		Type:    AccountDestructed,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("DeleteAccount", trieModifications, statedb)
}

func TestImplicitlyCreateAccountWithNonce(t *testing.T) {
	// When there is a change in an account that does not exist, a placeholder account leaf is added
	// as a witness. The last branch contains information about the leaf at `modified_node` being just
	// a placeholder and the circuit ensures that when the leaf is a placeholder, the branch (last branch)
	// children at `modified_node` is nil.
	blockNum := 1
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	addr := common.HexToAddress("0xaabccf12580138bc2bbceeeaa111df4e42ab81ab")

	trieMod := TrieModification{
		Type:    NonceChanged,
		Nonce:   142,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ImplicitlyCreateAccountWithNonce", trieModifications, statedb)
}

func TestImplicitlyCreateAccountWithBalance(t *testing.T) {
	blockNum := 1
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	addr := common.HexToAddress("0xaabccf12580138bc2bbceeeaa111df4e42ab81ab")

	trieMod := TrieModification{
		Type:    BalanceChanged,
		Balance: big.NewInt(7),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ImplicitlyCreateAccountWithBalance", trieModifications, statedb)
}

func TestImplicitlyCreateAccountWithCodeHash(t *testing.T) {
	blockNum := 1
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	addr := common.HexToAddress("0xaabccf12580138bc2bbceeeaa111df4e42ab81ab")
	codeHash := []byte{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}

	trieMod := TrieModification{
		Type:     BalanceChanged,
		CodeHash: codeHash,
		Address:  addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("ImplicitlyCreateAccountWithCodeHash", trieModifications, statedb)
}

func TestAccountAddPlaceholderBranch(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	// We need an account that doesn't exist yet.
	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Type:    BalanceChanged, // implicitly creating account
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountAddPlaceholderBranch", trieModifications, statedb)
}

func TestAccountDeletePlaceholderBranch(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	statedb.CreateAccount(addr)

	trieMod := TrieModification{
		Type:    AccountDestructed,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountDeletePlaceholderBranch", trieModifications, statedb)
}

func TestAccountAddPlaceholderExtension(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	// We need an account that doesn't exist yet.
	i := 40
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Type:    BalanceChanged, // implicitly creating account
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountAddPlaceholderExtension", trieModifications, statedb)
}

func TestAccountDeletePlaceholderExtension(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 40
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	statedb.CreateAccount(addr)

	trieMod := TrieModification{
		Type:    AccountDestructed,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("AccountDeletePlaceholderExtension", trieModifications, statedb)
}

// Branch has nil at the specified address.
func TestNonExistingAccountNilObject(t *testing.T) {
	// At the account address, there is a nil object.
	blockNum := 1
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	addr := common.HexToAddress("0xaaaccf12580138bc2bbceeeaa111df4e42ab81ab")
	statedb.IntermediateRoot(false)

	trieMod := TrieModification{
		Address: addr,
		Type:    AccountDoesNotExist,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("NonExistingAccountNilObject", trieModifications, statedb)
}

// Branch has a leaf at the specified address (not really at the specified address, but at the one
// that partially overlaps with the specified one).
func TestNonExistingAccount(t *testing.T) {
	// The leaf is returned that doesn't have the required address - but the two addresses overlaps in all nibbles up to
	// to the position in branch.
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	i := 21
	h := fmt.Sprintf("0x%d", i)
	addr := common.HexToAddress(h)

	trieMod := TrieModification{
		Address: addr,
		Type:    AccountDoesNotExist,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("NonExistingAccount", trieModifications, statedb)
}

// Account proof after placeholder branch deeper in the trie (branch placeholder not in the
// first or second level).
func TestAccountBranchPlaceholderDeeper(t *testing.T) {
	blockNum := 13284469
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)

	h := fmt.Sprintf("0xa21%d", 0)
	addr := common.HexToAddress(h)
	// Implicitly create account such that the account from the first level will be
	// replaced by a branch.
	trieMod := TrieModification{
		Type:    BalanceChanged,
		Balance: big.NewInt(23),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitnessSpecial("AccountBranchPlaceholderDeeper", trieModifications, statedb, 0)
}

func TestLeafInLastLevel(t *testing.T) {
	/*
		We have an extension node as a root. This extension node key in compact form
		is an array of length 32 (160 - 128): 16, 0, 0, ..., 0.
		That means 63 nibbles that are all zero: 0 (16 - 16), 0, ..., 0.
		The last nibble of key1 (1) and key2 (3) presents the position in branch.
		In this case, in a leaf, there is only one key byte: 32.

		storageProof[0]
			[]uint8 len: 56, cap: 56, [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
		storageProof[1]
			[]uint8 len: 22, cap: 22, [213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
		storageProof[2]
			[]uint8 len: 3, cap: 3, [194,32,1]

		Other examples:
		last level, long value
		[]uint8 len: 36, cap: 36, [227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
		not last level, short value
		[]uint8 len: 5, cap: 5, [196,130,32,0,1]

		Note: the "normal" leaf looks like:
		short:
		[226,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,1]

		long:
		[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...
	*/
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	statedb.CreateAccount(addr)

	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	key1 := common.HexToHash("0x1")
	val1 := common.BigToHash(big.NewInt(int64(1)))

	statedb.SetState(addr, key1, val1)

	key2 := common.HexToHash("0x3")
	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)
	/*
		The two keys are the same except in the last nibble:
		key1 = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]
		key2 = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3]
	*/

	storageProof, _, _, _, err := statedb.GetStorageProof(addr, key1)
	check(err)

	fmt.Println(storageProof[0])

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key1,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("LeafInLastLevel", trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func TestLeafWithOneNibble(t *testing.T) {
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	statedb.CreateAccount(addr)

	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	key1 := common.HexToHash("0x10")
	val1 := common.BigToHash(big.NewInt(int64(1)))

	statedb.SetState(addr, key1, val1)

	key2 := common.HexToHash("0x30")
	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	storageProof, _, _, _, err := statedb.GetStorageProof(addr, key1)
	check(err)

	fmt.Println(storageProof[0])

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key1,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("LeafWithOneNibble", trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

/*
storageProof[0]
[]uint8 len: 56, cap: 56, [247,149,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,160,131,32,100,192,26,10,249,123,103,55,126,227,156,51,43,248,141,13,184,86,199,239,167,52,34,242,212,138,29,106,251,72]
storageProof[1]
[]uint8 len: 46, cap: 46, [237,128,206,140,48,0,0,0,0,0,0,0,0,0,0,0,17,128,206,140,48,0,0,0,0,0,0,0,0,0,0,0,17,128,128,128,128,128,128,128,128,128,128,128,128,128]
storageProof[2]
[]uint8 len: 15, cap: 15, [206,140,48,0,0,0,0,0,0,0,0,0,0,0,17]
*/
func TestLeafWithMoreNibbles(t *testing.T) {
	// non-hashed leaf, leaf not in last level

	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x50efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	statedb.CreateAccount(addr)

	oracle.PreventHashingInSecureTrie = true

	// Let us make the extension node shorter than 55 (although this than causes branch to be hashed):
	key1 := common.HexToHash("0x100000000000000000000000")

	val1 := common.BigToHash(big.NewInt(int64(17)))

	statedb.SetState(addr, key1, val1)

	key2 := common.HexToHash("0x300000000000000000000000")
	statedb.SetState(addr, key2, val1)
	statedb.IntermediateRoot(false)

	storageProof, _, _, _, err := statedb.GetStorageProof(addr, key1)
	check(err)

	fmt.Println(storageProof[0])

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key1,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("LeafWithMoreNibbles", trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func TestBranchAfterExtNode(t *testing.T) {
	blockNum := 0
	blockNumberParent := big.NewInt(int64(blockNum))
	blockHeaderParent := oracle.PrefetchBlock(blockNumberParent, true, nil)
	database := state.NewDatabase(blockHeaderParent)
	statedb, _ := state.New(blockHeaderParent.Root, database, nil)
	addr := common.HexToAddress("0x40efbf12580138bc623c95757286df4e24eb81c9")

	statedb.DisableLoadingRemoteAccounts()

	statedb.CreateAccount(addr)

	oracle.PreventHashingInSecureTrie = true // to store the unchanged key

	key1Hex := "0x1000000000000000000000000"
	key2Hex := "0x2000000000000000000000000"
	key1 := common.HexToHash(key1Hex)
	key2 := common.HexToHash(key2Hex)

	val1 := common.BigToHash(big.NewInt(int64(111)))
	val2 := common.BigToHash(big.NewInt(int64(222)))

	statedb.SetState(addr, key1, val1)
	fmt.Println(key1)

	statedb.SetState(addr, key2, val2)
	fmt.Println(key2)

	statedb.IntermediateRoot(false)

	key1Hex += "1"
	key3 := common.HexToHash(key1Hex)
	statedb.SetState(addr, key3, val2)
	fmt.Println(key3)

	statedb.IntermediateRoot(false)

	val := common.BigToHash(big.NewInt(int64(17)))
	trieMod := TrieModification{
		Type:    StorageChanged,
		Key:     key1,
		Value:   val,
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	prepareWitness("BranchAfterExtNode", trieModifications, statedb)

	oracle.PreventHashingInSecureTrie = false
}

func TestNonExistingStorage(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12")}
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// First we have a branch with children at position 3 and 11.
	// ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75acef12a01883c2b3fc57957826df4e24e8baaa")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	// This key is not in the trie yet, its nibbles:
	// [3,10,6,3,5,7,...
	trieMod := TrieModification{
		Type:    StorageDoesNotExist,
		Key:     common.HexToHash("0x21"),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("NonExistingStorage", ks[:], values, addresses, trieModifications)
}

func TestNonExistingStorageLong(t *testing.T) {
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12")}

	var values []common.Hash
	v1 := common.FromHex("0xbbefaa12580138bc263c95757826df4e24eb81c9aaaaaaaaaaaaaaaaaaaaaaaa")
	v2 := common.BytesToHash(v1)
	for i := 0; i < len(ks); i++ {
		values = append(values, v2)
	}
	addr := common.HexToAddress("0x75acef12a01883c2b3fc57957826df4e24e8b19c")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	trieMod := TrieModification{
		Type:    StorageDoesNotExist,
		Key:     common.HexToHash("0x21"),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("NonExistingStorageLong", ks[:], values, addresses, trieModifications)
}

func TestNonExistingStorageNil(t *testing.T) {
	// Nil in branch.
	ks := [...]common.Hash{common.HexToHash("0x11"), common.HexToHash("0x12")}
	// hexed keys:
	// [3,1,14,12,12,...
	// [11,11,8,10,6,...
	// First we have a branch with children at position 3 and 11.
	// ks := [...]common.Hash{common.HexToHash("0x12"), common.HexToHash("0x21")}

	var values []common.Hash
	for i := 0; i < len(ks); i++ {
		values = append(values, common.BigToHash(big.NewInt(int64(i+1)))) // don't put 0 value because otherwise nothing will be set (if 0 is prev value), see state_object.go line 279
	}
	addr := common.HexToAddress("0x75acef12a01883c2b3fc57957826df4e24e8baaa")
	var addresses []common.Address
	for i := 0; i < len(ks); i++ {
		addresses = append(addresses, addr)
	}

	// This key is not in the trie yet, its nibbles:
	// [3,10,6,3,5,7,...
	trieMod := TrieModification{
		Type:    StorageDoesNotExist,
		Key:     common.HexToHash("0x22"),
		Address: addr,
	}
	trieModifications := []TrieModification{trieMod}

	updateStateAndPrepareWitness("NonExistingStorageNil", ks[:], values, addresses, trieModifications)
}
