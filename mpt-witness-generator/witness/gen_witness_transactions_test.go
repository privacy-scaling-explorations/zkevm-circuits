package witness

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/trie"
	"github.com/privacy-scaling-explorations/mpt-witness-generator/types"
)

func TestTransactions(t *testing.T) {
	t.Skip("failing test")
	txs := make([]*types.Transaction, 70)
	key, _ := crypto.GenerateKey()
	signer := types.LatestSigner(params.TestChainConfig)

	for i := range txs {
		amount := math.BigPow(2, int64(i))
		price := big.NewInt(300000)
		data := make([]byte, 100)
		tx := types.NewTransaction(uint64(i), common.Address{}, amount, 123457, price, data)
		signedTx, err := types.SignTx(tx, signer, key)
		if err != nil {
			panic(err)
		}
		txs[i] = signedTx
	}

	db := rawdb.NewMemoryDatabase()
	stackTrie := trie.NewStackTrie(db)

	stackTrie.UpdateAndGetProofs(db, types.Transactions(txs))

	fmt.Println("===")
}

// No update for each step, just final proof.
func TestGetProof(t *testing.T) {
	txs := make([]*types.Transaction, 70)
	key, _ := crypto.GenerateKey()
	signer := types.LatestSigner(params.TestChainConfig)

	for i := range txs {
		amount := math.BigPow(2, int64(i))
		price := big.NewInt(300000)
		data := make([]byte, 100)
		tx := types.NewTransaction(uint64(i), common.Address{}, amount, 123457, price, data)
		signedTx, err := types.SignTx(tx, signer, key)
		if err != nil {
			panic(err)
		}
		txs[i] = signedTx
	}

	db := rawdb.NewMemoryDatabase()
	stackTrie := trie.NewStackTrie(db)

	// Update the trie with transactions:
	types.DeriveSha(types.Transactions(txs), stackTrie)

	var indexBuf []byte
	indexBuf = rlp.AppendUint64(indexBuf[:0], uint64(1))

	proofS, err := stackTrie.GetProof(db, indexBuf)
	if err != nil {
		fmt.Println(err)
		return
	}

	fmt.Println(proofS)

	fmt.Println("===")
}
