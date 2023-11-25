package main

import "C"
import (
	"encoding/json"
	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/witness"
)

type Config struct {
	NodeUrl  string   `json:"NodeUrl"`
	BlockNum int      `json:"BlockNum"`
	Addr     string   `json:"Addr"`
	Keys     []string `json:"Keys"`
	Values   []string `json:"Values"`
}

//export GetWitness
func GetWitness(proofConf *C.char) *C.char {
	var config Config

	err := json.Unmarshal([]byte(C.GoString(proofConf)), &config)
	fmt.Println(err)
	fmt.Println(config)

	trieModifications := []witness.TrieModification{}

	addr := common.HexToAddress(config.Addr)
	for i := 0; i < len(config.Keys); i++ {
		trieMod := witness.TrieModification{
			Type:    witness.StorageChanged,
			Key:     common.HexToHash(config.Keys[i]),
			Value:   common.HexToHash(config.Values[i]),
			Address: addr,
		}
		trieModifications = append(trieModifications, trieMod)
	}

	proof := witness.GetWitness(config.NodeUrl, config.BlockNum, trieModifications)
	b, err := json.Marshal(proof)
	if err != nil {
		fmt.Println(err)
	}

	return C.CString(string(b))
}

func main() {}
