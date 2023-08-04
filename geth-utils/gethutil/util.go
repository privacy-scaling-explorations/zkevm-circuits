package gethutil

import (
	"math/big"

	"github.com/ethereum/go-ethereum/common/hexutil"
)

func toBigInt(value *hexutil.Big) *big.Int {
	if value != nil {
		return value.ToInt()
	}
	return big.NewInt(0)
}
