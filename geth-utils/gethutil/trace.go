package gethutil

import (
	"fmt"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/core/vm/runtime"
)

// Copied from github.com/ethereum/go-ethereum/internal/ethapi.StructLogRes
type StructLogRes struct {
	Pc      uint64             `json:"pc"`
	Op      string             `json:"op"`
	Gas     uint64             `json:"gas"`
	GasCost uint64             `json:"gasCost"`
	Depth   int                `json:"depth"`
	Error   string             `json:"error,omitempty"`
	Stack   *[]string          `json:"stack,omitempty"`
	Memory  *[]string          `json:"memory,omitempty"`
	Storage *map[string]string `json:"storage,omitempty"`
}

// FormatLogs formats EVM returned structured logs for json output.
// Copied from github.com/ethereum/go-ethereum/internal/ethapi.FormatLogs
func FormatLogs(logs []vm.StructLog) []StructLogRes {
	formatted := make([]StructLogRes, len(logs))
	for index, trace := range logs {
		formatted[index] = StructLogRes{
			Pc:      trace.Pc,
			Op:      trace.Op.String(),
			Gas:     trace.Gas,
			GasCost: trace.GasCost,
			Depth:   trace.Depth,
			Error:   trace.ErrorString(),
		}
		if trace.Stack != nil {
			stack := make([]string, len(trace.Stack))
			for i, stackValue := range trace.Stack {
				stack[i] = stackValue.Hex()
			}
			formatted[index].Stack = &stack
		}
		if trace.Memory != nil {
			memory := make([]string, 0, (len(trace.Memory)+31)/32)
			for i := 0; i+32 <= len(trace.Memory); i += 32 {
				memory = append(memory, fmt.Sprintf("%x", trace.Memory[i:i+32]))
			}
			formatted[index].Memory = &memory
		}
		if trace.Storage != nil {
			storage := make(map[string]string)
			for i, storageValue := range trace.Storage {
				storage[fmt.Sprintf("%x", i)] = fmt.Sprintf("%x", storageValue)
			}
			formatted[index].Storage = &storage
		}
	}
	return formatted
}

type Account struct {
	Address  common.Address
	Balance  *big.Int
	Bytecode []byte
}

func TraceTx(toAddress *common.Address, calldata []byte, config *runtime.Config, accounts []Account) ([]StructLogRes, error) {
	// Overwrite state
	newState, err := state.New(common.Hash{}, state.NewDatabase(rawdb.NewMemoryDatabase()), nil)
	if err != nil {
		return nil, fmt.Errorf("failed to initialize new state: %w", err)
	}
	for _, account := range accounts {
		if account.Balance != nil {
			newState.SetBalance(account.Address, account.Balance)
		}
		newState.SetCode(account.Address, account.Bytecode)
	}
	newState.Finalise(true)
	config.State = newState

	// Overwrite config with tracer
	tracer := vm.NewStructLogger(&vm.LogConfig{
		EnableMemory:     true,
		EnableReturnData: true,
	})
	config.EVMConfig.Debug = true
	config.EVMConfig.Tracer = tracer

	if toAddress == nil {
		_, _, _, err = runtime.Create(calldata, config)
	} else {
		_, _, err = runtime.Call(*toAddress, nil, config)
	}

	return FormatLogs(tracer.StructLogs()), err
}

// TODO: TraceBlock
