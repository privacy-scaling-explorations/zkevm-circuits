package witness

import (
	"fmt"
	"strings"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/oracle"
)

type BranchNode struct {
	ModifiedIndex int
	DriftedIndex  int
	ListRlpBytes  [2][]byte
}

func (n *BranchNode) MarshalJSON() ([]byte, error) {
	listRlpBytes1 := base64ToString(n.ListRlpBytes[0])
	listRlpBytes2 := base64ToString(n.ListRlpBytes[1])
	jsonResult := fmt.Sprintf(`{"modified_index": %d, "drifted_index": %d, "list_rlp_bytes":[%s,%s]}`,
		n.ModifiedIndex, n.DriftedIndex, listRlpBytes1, listRlpBytes2)
	return []byte(jsonResult), nil
}

type ExtensionNode struct {
	ListRlpBytes []byte
}

func (n *ExtensionNode) MarshalJSON() ([]byte, error) {
	listRlpBytes := base64ToString(n.ListRlpBytes)
	jsonResult := fmt.Sprintf(`{"list_rlp_bytes":%s}`, listRlpBytes)
	return []byte(jsonResult), nil
}

// When marshalling, []byte encodes as a base64-encoded string.
func base64ToString(bs []byte) string {
	var s string
	if bs == nil {
		f := make([]string, valueLen)
		s = "["
		for i := 0; i < len(f); i++ {
			if i != len(f)-1 {
				s += "0, "
			} else {
				s += "0]"
			}
		}
	} else {
		s = strings.Join(strings.Fields(fmt.Sprintf("%d", bs)), ",")
	}

	return s
}

type StartNode struct {
	DisablePreimageCheck bool   `json:"disable_preimage_check"`
	ProofType            string `json:"proof_type"`
}

type ExtensionBranchNode struct {
	IsExtension bool `json:"is_extension"`
	// IsModExtension = true for the extension node that gets replaced by a shorter (in terms of nibbles)
	// extension node. IsModExtension is not set to true for the newly appeared extension node (nibbles
	// of the extension node that caused replacement + nibbles of the newly appeared extension node =
	// nibbles of the original extension node).
	IsModExtension [2]bool       `json:"is_mod_extension"`
	IsPlaceholder  [2]bool       `json:"is_placeholder"`
	Extension      ExtensionNode `json:"extension"`
	Branch         BranchNode    `json:"branch"`
}

type AccountNode struct {
	Address           common.Address
	Key               []byte
	ListRlpBytes      [2][]byte
	ValueRlpBytes     [2][]byte
	ValueListRlpBytes [2][]byte
	DriftedRlpBytes   []byte
	WrongRlpBytes     []byte
	IsModExtension    [2]bool `json:"is_mod_extension"`
	ModListRlpBytes   [2][]byte
}

func (n *AccountNode) MarshalJSON() ([]byte, error) {
	address := base64ToString(n.Address.Bytes())
	key := base64ToString(n.Key)
	listRlpBytes1 := base64ToString(n.ListRlpBytes[0])
	listRlpBytes2 := base64ToString(n.ListRlpBytes[1])
	valueRlpBytes1 := base64ToString(n.ValueRlpBytes[0])
	valueRlpBytes2 := base64ToString(n.ValueRlpBytes[1])
	valueListRlpBytes1 := base64ToString(n.ValueListRlpBytes[0])
	valueListRlpBytes2 := base64ToString(n.ValueListRlpBytes[1])
	driftedRlpBytes := base64ToString(n.DriftedRlpBytes)
	wrongRlpBytes := base64ToString(n.WrongRlpBytes)
	modListRlpBytes1 := base64ToString(n.ModListRlpBytes[0])
	modListRlpBytes2 := base64ToString(n.ModListRlpBytes[1])
	jsonResult := fmt.Sprintf(`{"address":%s, "key":%s, "list_rlp_bytes":[%s,%s], "value_rlp_bytes":[%s,%s], "value_list_rlp_bytes":[%s,%s], "drifted_rlp_bytes":%s, "wrong_rlp_bytes":%s, "is_mod_extension": [%t, %t], "mod_list_rlp_bytes":[%s,%s]}`,
		address, key, listRlpBytes1, listRlpBytes2, valueRlpBytes1, valueRlpBytes2, valueListRlpBytes1, valueListRlpBytes2,
		driftedRlpBytes, wrongRlpBytes, n.IsModExtension[0], n.IsModExtension[1], modListRlpBytes1, modListRlpBytes2)
	return []byte(jsonResult), nil
}

type StorageNode struct {
	Address         common.Hash `json:"address"`
	Key             []byte      `json:"key"`
	ListRlpBytes    [2][]byte   `json:"list_rlp_bytes"`
	ValueRlpBytes   [2][]byte   `json:"value_rlp_bytes"`
	DriftedRlpBytes []byte      `json:"drifted_rlp_bytes"`
	WrongRlpBytes   []byte      `json:"wrong_rlp_bytes"`
	IsModExtension  [2]bool     `json:"is_mod_extension"`
	ModListRlpBytes [2][]byte
}

func (n *StorageNode) MarshalJSON() ([]byte, error) {
	address := base64ToString(n.Address.Bytes())
	key := base64ToString(n.Key)
	listRlpBytes1 := base64ToString(n.ListRlpBytes[0])
	listRlpBytes2 := base64ToString(n.ListRlpBytes[1])
	valueRlpBytes1 := base64ToString(n.ValueRlpBytes[0])
	valueRlpBytes2 := base64ToString(n.ValueRlpBytes[1])
	driftedRlpBytes := base64ToString(n.DriftedRlpBytes)
	wrongRlpBytes := base64ToString(n.WrongRlpBytes)
	modListRlpBytes1 := base64ToString(n.ModListRlpBytes[0])
	modListRlpBytes2 := base64ToString(n.ModListRlpBytes[1])
	jsonResult := fmt.Sprintf(`{"address":%s, "key":%s, "list_rlp_bytes":[%s,%s], "value_rlp_bytes":[%s,%s], "drifted_rlp_bytes":%s, "wrong_rlp_bytes":%s, "is_mod_extension": [%t, %t], "mod_list_rlp_bytes":[%s,%s]}`,
		address, key, listRlpBytes1, listRlpBytes2, valueRlpBytes1, valueRlpBytes2, driftedRlpBytes, wrongRlpBytes, n.IsModExtension[0], n.IsModExtension[1],
		modListRlpBytes1, modListRlpBytes2)
	return []byte(jsonResult), nil
}

type JSONableValues [][]byte

func (u JSONableValues) MarshalJSON() ([]byte, error) {
	var result string
	if u == nil {
		result = "[]"
	} else {
		result = strings.Join(strings.Fields(fmt.Sprintf("%d", u)), ",")
	}
	return []byte(result), nil
}

/*
Note: using pointers for fields to be null when not set (otherwise the field is set to default value
when marshalling).
*/
type Node struct {
	Start           *StartNode           `json:"start"`
	ExtensionBranch *ExtensionBranchNode `json:"extension_branch"`
	Account         *AccountNode         `json:"account"`
	Storage         *StorageNode         `json:"storage"`
	Values          JSONableValues       `json:"values"`
	KeccakData      JSONableValues       `json:"keccak_data"`
}

func GetStartNode(proofType string, sRoot, cRoot common.Hash, specialTest byte) Node {
	s := StartNode{
		DisablePreimageCheck: oracle.PreventHashingInSecureTrie || specialTest == 5,
		ProofType:            proofType,
	}
	var values [][]byte
	var values1 []byte
	var values2 []byte
	values1 = append(values1, 160)
	values1 = append(values1, sRoot.Bytes()...)
	values1 = append(values1, 0)
	values2 = append(values2, 160)
	values2 = append(values2, cRoot.Bytes()...)
	values2 = append(values2, 0)

	values = append(values, values1)
	values = append(values, values2)

	return Node{
		Start:  &s,
		Values: values,
	}
}

func GetEndNode() Node {
	e := StartNode{
		DisablePreimageCheck: false,
		ProofType:            "Disabled",
	}

	endValues1, endValues2 := make([]byte, valueLen), make([]byte, valueLen)
	endValues1[0], endValues2[0] = 160, 160
	endValues := [][]byte{endValues1, endValues2}

	return Node{
		Start:  &e,
		Values: endValues,
	}
}
