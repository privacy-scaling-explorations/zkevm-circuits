package witness

import (
	"encoding/hex"
	"encoding/json"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/oracle"
)

type BranchNode struct {
	ModifiedIndex int
	DriftedIndex  int
	ListRlpBytes  [2][]byte
}

func (n *BranchNode) MarshalJSON() ([]byte, error) {
	jsonData := struct {
		ModifiedIndex int      `json:"modified_index"`
		DriftedIndex  int      `json:"drifted_index"`
		ListRlpBytes  []string `json:"list_rlp_bytes"`
	}{
		ModifiedIndex: n.ModifiedIndex,
		DriftedIndex:  n.DriftedIndex,
		ListRlpBytes:  encodeArray(n.ListRlpBytes[:]),
	}
	return json.Marshal(jsonData)
}

type ExtensionNode struct {
	ListRlpBytes []byte
}

func (n *ExtensionNode) MarshalJSON() ([]byte, error) {
	jsonData := struct {
		ListRlpBytes string `json:"list_rlp_bytes"`
	}{
		ListRlpBytes: base64ToString(n.ListRlpBytes),
	}
	return json.Marshal(jsonData)
}

// When marshalling, []byte encodes as a base64-encoded string.
func base64ToString(bs []byte) string {
	if bs == nil {
		bs = make([]byte, valueLen)
	}
	return hex.EncodeToString(bs)
}

func encodeArray(arrayBytes [][]byte) []string {
	hexStrings := make([]string, len(arrayBytes))
	for i, item := range arrayBytes {
		hexStrings[i] = base64ToString(item)
	}
	return hexStrings
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

type ModExtensionNode struct {
	ListRlpBytes [2][]byte
}

func (n *ModExtensionNode) MarshalJSON() ([]byte, error) {
	jsonData := struct {
		ListRlpBytes []string `json:"list_rlp_bytes"`
	}{
		ListRlpBytes: encodeArray(n.ListRlpBytes[:]),
	}
	return json.Marshal(jsonData)
}

type AccountNode struct {
	Address           common.Address
	Key               []byte
	ListRlpBytes      [2][]byte
	ValueRlpBytes     [2][]byte
	ValueListRlpBytes [2][]byte
	DriftedRlpBytes   []byte
	WrongRlpBytes     []byte
	IsModExtension    [2]bool
}

func (n *AccountNode) MarshalJSON() ([]byte, error) {
	jsonData := struct {
		Address           string   `json:"address"`
		Key               string   `json:"key"`
		ListRlpBytes      []string `json:"list_rlp_bytes"`
		ValueRlpBytes     []string `json:"value_rlp_bytes"`
		ValueListRlpBytes []string `json:"value_list_rlp_bytes"`
		DriftedRlpBytes   string   `json:"drifted_rlp_bytes"`
		WrongRlpBytes     string   `json:"wrong_rlp_bytes"`
		IsModExtension    [2]bool  `json:"is_mod_extension"`
	}{
		Address:           base64ToString(n.Address.Bytes()),
		Key:               base64ToString(n.Key),
		ListRlpBytes:      encodeArray(n.ListRlpBytes[:]),
		ValueRlpBytes:     encodeArray(n.ValueRlpBytes[:]),
		ValueListRlpBytes: encodeArray(n.ValueListRlpBytes[:]),
		DriftedRlpBytes:   base64ToString(n.DriftedRlpBytes),
		WrongRlpBytes:     base64ToString(n.WrongRlpBytes),
		IsModExtension:    n.IsModExtension,
	}
	return json.Marshal(jsonData)
}

type StorageNode struct {
	Address         common.Hash
	Key             []byte
	ListRlpBytes    [2][]byte
	ValueRlpBytes   [2][]byte
	DriftedRlpBytes []byte
	WrongRlpBytes   []byte
	IsModExtension  [2]bool
}

func (n *StorageNode) MarshalJSON() ([]byte, error) {
	jsonData := struct {
		Address         string   `json:"address"`
		Key             string   `json:"key"`
		ListRlpBytes    []string `json:"list_rlp_bytes"`
		ValueRlpBytes   []string `json:"value_rlp_bytes"`
		DriftedRlpBytes string   `json:"drifted_rlp_bytes"`
		WrongRlpBytes   string   `json:"wrong_rlp_bytes"`
		IsModExtension  [2]bool  `json:"is_mod_extension"`
	}{
		Address:         base64ToString(n.Address.Bytes()),
		Key:             base64ToString(n.Key),
		ListRlpBytes:    encodeArray(n.ListRlpBytes[:]),
		ValueRlpBytes:   encodeArray(n.ValueRlpBytes[:]),
		DriftedRlpBytes: base64ToString(n.DriftedRlpBytes),
		WrongRlpBytes:   base64ToString(n.WrongRlpBytes),
		IsModExtension:  n.IsModExtension,
	}
	return json.Marshal(jsonData)
}

type JSONableValues [][]byte

func (u JSONableValues) MarshalJSON() ([]byte, error) {
	return json.Marshal(encodeArray(u))
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
	ModExtension    *ModExtensionNode    `json:"mod_extension"`
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
