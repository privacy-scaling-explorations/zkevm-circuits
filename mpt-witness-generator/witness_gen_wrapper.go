package main

// #include <stdlib.h>
import "C"
import (
	"encoding/json"
	"fmt"
	"unsafe"

	"github.com/privacy-scaling-explorations/mpt-witness-generator/witness"
)

type Config struct {
	NodeUrl  string   `json:"NodeUrl"`
	BlockNum int      `json:"BlockNum"`
	Addr     string   `json:"Addr"`
	Keys     []string `json:"Keys"`
	Values   []string `json:"Values"`
}

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

	fmt.Printf("%+v", config)
	proof := witness.GetWitness(config.NodeUrl, config.BlockNum, config.Mods)
	b, err := json.Marshal(proof)
	if err != nil {
		fmt.Println(err)
	}

	return C.CString(string(b))
}

//export FreeString
func FreeString(str *C.char) {
	C.free(unsafe.Pointer(str))
}

func main() {}
