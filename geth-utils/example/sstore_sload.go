package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm/runtime"

	"main/gethutil"
)

func main() {
	address := common.BytesToAddress([]byte{0xff})
	asm := gethutil.NewAssembly().SStore(0, 0xcafeb0ba).SLoad(0).SStore(0, 0xdeabbeef).SLoad(0)
	contracts := []gethutil.Account{{Address: address, Bytecode: asm.Bytecode}}

	logs, err := gethutil.TraceTx(&address, nil, &runtime.Config{GasLimit: 25000}, contracts)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to trace tx, err: %v\n", err)
	}

	bytes, err := json.MarshalIndent(logs, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to marshal logs, err: %v\n", err)
	}

	fmt.Fprintln(os.Stdout, string(bytes))
}
