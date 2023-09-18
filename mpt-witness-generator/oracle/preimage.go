package oracle

import (
	"errors"
	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var preimages = make(map[common.Hash][]byte)

func Preimage(hash common.Hash) ([]byte, error) {
	val, ok := preimages[hash]
	if !ok {
		fmt.Println("can't find preimage", hash)
		return nil, errors.New("can't find preimage")
	}
	comphash := crypto.Keccak256Hash(val)
	if hash != comphash {
		fmt.Println("corruption in hash " + hash.String())
		return nil, errors.New("corruption in hash " + hash.String())
	}
	return val, nil
}

// TODO: Maybe we will want to have a seperate preimages for next block's preimages?
func Preimages() map[common.Hash][]byte {
	return preimages
}

// KeyValueWriter wraps the Put method of a backing data store.
type PreimageKeyValueWriter struct{}

// Put inserts the given value into the key-value data store.
func (kw PreimageKeyValueWriter) Put(key []byte, value []byte) error {
	hash := crypto.Keccak256Hash(value)
	if hash != common.BytesToHash(key) {
		panic("bad preimage value write")
	}
	preimages[hash] = common.CopyBytes(value)
	// fmt.Println("tx preimage", hash, common.Bytes2Hex(value))
	return nil
}

// Delete removes the key from the key-value data store.
func (kw PreimageKeyValueWriter) Delete(key []byte) error {
	return nil
}
