package main

/*
   #include <stdlib.h>
*/
import "C"
import (
	"encoding/json"
	"fmt"
	"main/gethutil"
	"math/big"
	"os"
	"unsafe"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/core/vm/runtime"
	"github.com/ethereum/go-ethereum/params"
)

// TODO: Add proper error handling.  For example, return an int, where 0 means
// ok, and !=0 means error.
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

// FIXME: GethConfig unmarshals from JsonConfig, which is extremely confusing.
// https://github.com/appliedzkp/zkevm-circuits/issues/188
type GethConfig struct {
	config    runtime.Config
	contracts []gethutil.Account
	target    common.Address
}

type BlockConstants struct {
	Hash        common.Hash    `json:"hash"`
	Coinbase    common.Address `json:"coinbase"`
	Timestamp   *hexutil.Big   `json:"timestamp"`
	BlockNumber *hexutil.Big   `json:"number"`
	Difficulty  *hexutil.Big   `json:"difficulty"`
	GasLimit    *hexutil.Big   `json:"gas_limit"`
	ChainID     *hexutil.Big   `json:"chain_id"`
	BaseFee     *hexutil.Big   `json:"base_fee"`
}

type Transaction struct {
	Origin   common.Address `json:"origin"`
	GasLimit *hexutil.Big   `json:"gas_limit"`
	Target   common.Address `json:"target"`
}

type AccountData struct {
	Address common.Address `json:"address"`
	Balance *hexutil.Big   `json:"balance"`
	Code    hexutil.Bytes  `json:"code"`
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
		Origin:      jConfig.Transaction.Origin,
		GasLimit:    jConfig.Transaction.GasLimit.ToInt().Uint64(),
		Difficulty:  jConfig.Block.Difficulty.ToInt(),
		Time:        jConfig.Block.Timestamp.ToInt(),
		Coinbase:    jConfig.Block.Coinbase,
		BlockNumber: jConfig.Block.BlockNumber.ToInt(),
		ChainConfig: &params.ChainConfig{
			ChainID:             jConfig.Block.ChainID.ToInt(),
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
		address := contract.Address
		balance := contract.Balance.ToInt()
		code := contract.Code
		this.contracts = append(this.contracts, gethutil.Account{Address: address, Balance: balance, Bytecode: code})
	}

	this.target = jConfig.Transaction.Target

	return nil
}

func main() {}
