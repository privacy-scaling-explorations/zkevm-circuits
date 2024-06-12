package oracle

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"math/big"
	"net/http"
	"os"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/rlp"
)

type jsonreq struct {
	Jsonrpc string        `json:"jsonrpc"`
	Method  string        `json:"method"`
	Params  []interface{} `json:"params"`
	Id      uint64        `json:"id"`
}

type jsonresp struct {
	Jsonrpc string        `json:"jsonrpc"`
	Id      uint64        `json:"id"`
	Result  AccountResult `json:"result"`
}

type jsonresps struct {
	Jsonrpc string `json:"jsonrpc"`
	Id      uint64 `json:"id"`
	Result  string `json:"result"`
}

type jsonrespi struct {
	Jsonrpc string         `json:"jsonrpc"`
	Id      uint64         `json:"id"`
	Result  hexutil.Uint64 `json:"result"`
}

type jsonrespt struct {
	Jsonrpc string `json:"jsonrpc"`
	Id      uint64 `json:"id"`
	Result  Header `json:"result"`
}

// Result structs for GetProof
type AccountResult struct {
	Address      common.Address  `json:"address"`
	AccountProof []string        `json:"accountProof"`
	Balance      *hexutil.Big    `json:"balance"`
	CodeHash     common.Hash     `json:"codeHash"`
	Nonce        hexutil.Uint64  `json:"nonce"`
	StorageHash  common.Hash     `json:"storageHash"`
	StorageProof []StorageResult `json:"storageProof"`
}

type StorageResult struct {
	Key   string       `json:"key"`
	Value *hexutil.Big `json:"value"`
	Proof []string     `json:"proof"`
}

// Account is the Ethereum consensus representation of accounts.
// These objects are stored in the main account trie.
type Account struct {
	Nonce    uint64
	Balance  *big.Int
	Root     common.Hash // merkle root of the storage trie
	CodeHash []byte
}

var NodeUrl = "https://mainnet.infura.io/v3/9aa3d95b3bc440fa88ea12eaa4456161"
var RemoteUrl = "https://mainnet.infura.io/v3/9aa3d95b3bc440fa88ea12eaa4456161"
var LocalUrl = "http://localhost:8545"

// For generating special tests for MPT circuit:
var PreventHashingInSecureTrie = false // storage
var AccountPreventHashingInSecureTrie = false

func toFilename(key string) string {
	return fmt.Sprintf("/tmp/eth/json_%s", key)
}

func cacheRead(key string) []byte {
	dat, err := os.ReadFile(toFilename(key))
	if err == nil {
		return dat
	}
	panic("cache missing")
}

func cacheExists(key string) bool {
	_, err := os.Stat(toFilename(key))
	return err == nil
}

func cacheWrite(key string, value []byte) {
	os.WriteFile(toFilename(key), value, 0644)
}

func getAPI(jsonData []byte) io.Reader {
	key := hexutil.Encode(crypto.Keccak256(jsonData))
	var (
		err     error
		resp    *http.Response
		retries int = 3
	)
	for retries > 0 {
		resp, err = http.Post(NodeUrl, "application/json", bytes.NewBuffer(jsonData))
		if err != nil {
			retries -= 1
			time.Sleep(1000)
		} else {
			break
		}
	}
	defer resp.Body.Close()
	ret, _ := io.ReadAll(resp.Body)
	cacheWrite(key, ret)
	return bytes.NewReader(ret)
}

var unhashMap = make(map[common.Hash]common.Address)

func unhash(addrHash common.Hash) common.Address {
	return unhashMap[addrHash]
}

var cached = make(map[string]bool)

func PrefetchStorage(blockNumber *big.Int, addr common.Address, skey common.Hash, postProcess func(map[common.Hash][]byte)) []string {
	key := fmt.Sprintf("proof_%d_%s_%s", blockNumber, addr, skey)
	// TODO: should return proof anyway
	if cached[key] {
		return nil
	}
	cached[key] = true

	ap := getProofAccount(blockNumber, addr, skey, true)
	//fmt.Println("PrefetchStorage", blockNumber, addr, skey, len(ap))
	newPreimages := make(map[common.Hash][]byte)
	for _, s := range ap {
		ret, _ := hex.DecodeString(s[2:])
		hash := crypto.Keccak256Hash(ret)
		//fmt.Println("   ", i, hash)
		newPreimages[hash] = ret
	}

	if postProcess != nil {
		postProcess(newPreimages)
	}

	for hash, val := range newPreimages {
		preimages[hash] = val
	}

	return ap
}

func PrefetchAccount(blockNumber *big.Int, addr common.Address, postProcess func(map[common.Hash][]byte)) []string {
	key := fmt.Sprintf("proof_%d_%s", blockNumber, addr)
	if cached[key] {
		return nil
	}
	cached[key] = true

	ap := getProofAccount(blockNumber, addr, common.Hash{}, false)
	newPreimages := make(map[common.Hash][]byte)
	for _, s := range ap {
		ret, _ := hex.DecodeString(s[2:])
		hash := crypto.Keccak256Hash(ret)
		newPreimages[hash] = ret

		/*
			// just for debugging:
			elems, _, err := rlp.SplitList(ret)
			if err != nil {
				fmt.Println("decode error", err)
			}
			switch c, _ := rlp.CountValues(elems); c {
			case 2:
				fmt.Println("2")
			case 17:
				fmt.Println("17")
			default:
				fmt.Println("invalid number of list elements")
			}
		*/
	}

	if postProcess != nil {
		postProcess(newPreimages)
	}

	for hash, val := range newPreimages {
		preimages[hash] = val
	}

	return ap
}

func PrefetchCode(blockNumber *big.Int, addrHash common.Hash) {
	key := fmt.Sprintf("code_%d_%s", blockNumber, addrHash)
	if cached[key] {
		return
	}
	cached[key] = true
	ret := getProvedCodeBytes(blockNumber, addrHash)
	hash := crypto.Keccak256Hash(ret)
	preimages[hash] = ret
}

var inputs [7]common.Hash

func Input(index int) common.Hash {
	if index < 0 || index > 5 {
		panic("bad input index")
	}
	return inputs[index]
}

func Output(output common.Hash) {
	if output == inputs[6] {
		fmt.Println("good transition")
	} else {
		fmt.Println(output, "!=", inputs[5])
		panic("BAD transition :((")
	}
}

func check(err error) {
	if err != nil {
		log.Fatal(err)
	}
}

func PrefetchBlock(blockNumber *big.Int, startBlock bool, hasher types.TrieHasher) types.Header {
	r := jsonreq{Jsonrpc: "2.0", Method: "eth_getBlockByNumber", Id: 1}
	r.Params = make([]interface{}, 2)
	r.Params[0] = fmt.Sprintf("0x%x", blockNumber.Int64())
	r.Params[1] = true
	jsonData, _ := json.Marshal(r)

	jr := jsonrespt{}
	check(json.NewDecoder(getAPI(jsonData)).Decode(&jr))
	blockHeader := jr.Result.ToHeader()

	// put in the start block header
	if startBlock {
		blockHeaderRlp, _ := rlp.EncodeToBytes(blockHeader)
		hash := crypto.Keccak256Hash(blockHeaderRlp)
		preimages[hash] = blockHeaderRlp
		inputs[0] = hash
		return blockHeader
	}

	// second block
	if blockHeader.ParentHash != Input(0) {
		fmt.Println(blockHeader.ParentHash, Input(0))
		panic("block transition isn't correct")
	}
	inputs[1] = blockHeader.TxHash
	inputs[2] = common.BytesToHash(blockHeader.Coinbase[:])
	inputs[3] = blockHeader.UncleHash
	inputs[4] = common.BigToHash(big.NewInt(int64(blockHeader.GasLimit)))
	inputs[5] = common.BigToHash(big.NewInt(int64(blockHeader.Time)))

	// secret input
	inputs[6] = blockHeader.Root

	// save the inputs
	saveinput := make([]byte, 0)
	for i := 0; i < len(inputs); i++ {
		saveinput = append(saveinput, inputs[i].Bytes()[:]...)
	}
	key := fmt.Sprintf("/tmp/eth/%d", blockNumber.Uint64()-1)
	os.WriteFile(key, saveinput, 0644)

	// save the txs
	txs := make([]*types.Transaction, len(jr.Result.Transactions))
	for i := 0; i < len(jr.Result.Transactions); i++ {
		txs[i] = jr.Result.Transactions[i].ToTransaction()
	}
	fmt.Println(txs[0].To())
	testTxHash := types.DeriveSha(types.Transactions(txs), hasher)
	if testTxHash != blockHeader.TxHash {
		fmt.Println(testTxHash, "!=", blockHeader.TxHash)
		panic("tx hash derived wrong")
	}

	return blockHeader
}

func getProofAccount(blockNumber *big.Int, addr common.Address, skey common.Hash, storage bool) []string {
	addrHash := crypto.Keccak256Hash(addr[:])
	unhashMap[addrHash] = addr

	r := jsonreq{Jsonrpc: "2.0", Method: "eth_getProof", Id: 1}
	r.Params = make([]interface{}, 3)
	r.Params[0] = addr
	r.Params[1] = [1]common.Hash{skey}
	r.Params[2] = fmt.Sprintf("0x%x", blockNumber.Int64())
	jsonData, _ := json.Marshal(r)
	jr := jsonresp{}
	json.NewDecoder(getAPI(jsonData)).Decode(&jr)

	if storage {
		if len(jr.Result.StorageProof) != 0 {
			return jr.Result.StorageProof[0].Proof
		} else {
			return []string{}
		}
	} else {
		return jr.Result.AccountProof
	}
}

func getProvedCodeBytes(blockNumber *big.Int, addrHash common.Hash) []byte {
	addr := unhash(addrHash)

	r := jsonreq{Jsonrpc: "2.0", Method: "eth_getCode", Id: 1}
	r.Params = make([]interface{}, 2)
	r.Params[0] = addr
	r.Params[1] = fmt.Sprintf("0x%x", blockNumber.Int64())
	jsonData, _ := json.Marshal(r)
	jr := jsonresps{}
	json.NewDecoder(getAPI(jsonData)).Decode(&jr)

	//fmt.Println(jr.Result)

	// curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getCode","params":["0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b", "0x2"],"id":1}'

	ret, _ := hex.DecodeString(jr.Result[2:])
	//fmt.Println(ret)
	return ret
}
