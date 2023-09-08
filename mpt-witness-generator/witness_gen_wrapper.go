package main

import "C"
import (
	"encoding/json"
	"fmt"

	"github.com/privacy-scaling-explorations/mpt-witness-generator/witness"
)

type GetWitnessRequest struct {
	BlockNum int    `json:"BlockNum"`
	NodeUrl  string `json:"NodeUrl"`
	Mods     []witness.TrieModification
}

//export GetWitness
func GetWitness(proofConf *C.char) *C.char {
	var config GetWitnessRequest

	err := json.Unmarshal([]byte(C.GoString(proofConf)), &config)
	if err != nil {
		panic(err)
	}

	proof := witness.GetWitness(config.NodeUrl, config.BlockNum, config.Mods)
	b, err := json.Marshal(proof)
	if err != nil {
		fmt.Println(err)
	}

	return C.CString(string(b))
}

func main() {}
