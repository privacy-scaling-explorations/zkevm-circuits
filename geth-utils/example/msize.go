package main

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm/runtime"

	"main/gethutil"
)

func main() {
	address := common.BytesToAddress([]byte{0xff})
	asm := gethutil.NewAssembly().MStore(0x40, 0x80).MSize().Stop()
	contracts := []gethutil.Account{{Address: address, Bytecode: asm.Bytecode}}
	fmt.Fprintln(os.Stdout, hex.EncodeToString(asm.Bytecode))

	logs, err := gethutil.TraceTx(&address, nil, &runtime.Config{GasLimit: 100}, contracts)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to trace tx, err: %v\n", err)
	}

	bytes, err := json.MarshalIndent(logs, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to marshal logs, err: %v\n", err)
	}

	fmt.Fprintln(os.Stdout, string(bytes))
}
