package main

/*
   #include <stdlib.h>
*/
import "C"
import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"main/gethutil"
	"math/big"
	"os"
	"unsafe"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/core/vm/runtime"
	"github.com/ethereum/go-ethereum/params"
)

//export CreateTrace
func CreateTrace(config *C.char) *C.char {
	var gethConfig GethConfig
	err := json.Unmarshal([]byte(C.GoString(config)), &gethConfig)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to load trace config, err: %v\n", err)
	}

	logs, err := gethutil.TraceTx(&gethConfig.target, nil, &gethConfig.config, gethConfig.contracts)
	if err != nil {
		fmt.Fprintf(os.Stderr, "trace stopped unexpectedly, err: %v\n", err)
	}

	bytes, err := json.MarshalIndent(logs, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to marshal logs, err: %v\n", err)
	}

	return C.CString(string(bytes))
}

//export FreeString
func FreeString(str *C.char) {
	C.free(unsafe.Pointer(str))
}

type GethConfig struct {
	config    runtime.Config
	contracts []gethutil.Account
	target    common.Address
}

type BlockConstants struct {
	Hash        string `json:"hash"`
	Coinbase    string `json:"coinbase"`
	Timestamp   string `json:"timestamp"`
	BlockNumber string `json:"number"`
	Difficulty  string `json:"difficulty"`
	GasLimit    string `json:"gas_limit"`
	ChainID     string `json:"chain_id"`
	BaseFee     string `json:"base_fee"`
}

type Transaction struct {
	Origin   string `json:"origin"`
	GasLimit string `json:"gas_limit"`
	Target   string `json:"target"`
}

type AccountData struct {
	Address string `json:"address"`
	Balance string `json:"balance"`
	Code    string `json:"code"`
}

type JsonConfig struct {
	Block       BlockConstants `json:"block_constants"`
	Transaction Transaction    `json:"transaction"`
	Accounts    []AccountData  `json:"accounts"`
}

func (this *GethConfig) UnmarshalJSON(b []byte) error {
	var jConfig JsonConfig
	err := json.Unmarshal(b, &jConfig)
	if err != nil {
		return err
	}

	this.config = runtime.Config{
		Origin:      AddressFromString(jConfig.Transaction.Origin, 16),
		GasLimit:    NewBigIntFromString(jConfig.Transaction.GasLimit, 16).Uint64(),
		Difficulty:  NewBigIntFromString(jConfig.Block.Difficulty, 16),
		Time:        NewBigIntFromString(jConfig.Block.Timestamp, 16),
		Coinbase:    AddressFromString(jConfig.Block.Coinbase, 16),
		BlockNumber: NewBigIntFromString(jConfig.Block.BlockNumber, 16),
		ChainConfig: &params.ChainConfig{
			ChainID:             NewBigIntFromString(jConfig.Block.ChainID, 16),
			HomesteadBlock:      big.NewInt(0),
			DAOForkBlock:        big.NewInt(0),
			DAOForkSupport:      true,
			EIP150Block:         big.NewInt(0),
			EIP150Hash:          common.HexToHash("0x2086799aeebeae135c246c65021c82b4e15a2c451340993aacfd2751886514f0"),
			EIP155Block:         big.NewInt(0),
			EIP158Block:         big.NewInt(0),
			ByzantiumBlock:      big.NewInt(0),
			ConstantinopleBlock: big.NewInt(0),
			PetersburgBlock:     big.NewInt(0),
			IstanbulBlock:       big.NewInt(0),
			MuirGlacierBlock:    big.NewInt(0),
			BerlinBlock:         big.NewInt(0),
			LondonBlock:         big.NewInt(0),
		},
		EVMConfig: vm.Config{},
	}

	for _, contract := range jConfig.Accounts {
		address := AddressFromString(contract.Address, 16)
		balance := NewBigIntFromString(contract.Balance, 16)
		code, err := hex.DecodeString(contract.Code)
		if err != nil {
			return err
		}
		this.contracts = append(this.contracts, gethutil.Account{Address: address, Balance: balance, Bytecode: code})
	}

	this.target = AddressFromString(jConfig.Transaction.Target, 16)

	return nil
}

func NewBigIntFromString(v string, base int) *big.Int {
	b, success := new(big.Int).SetString(v, base)
	if !success {
		fmt.Fprintf(os.Stderr, "failed to convert string '%s' to bigint\n", v)
		return nil
	}
	return b
}

func AddressFromString(v string, base int) common.Address {
	b := NewBigIntFromString(v, base)
	return common.BigToAddress(b)
}

func main() {}
