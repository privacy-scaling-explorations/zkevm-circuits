package witness

import (
	"bytes"
	"fmt"
	"main/gethutil/mpt/trie"
	"main/gethutil/mpt/types"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
)

func makeTransactions(n int) []*types.Transaction {
	txs := make([]*types.Transaction, n)
	key, _ := crypto.GenerateKey()
	signer := types.LatestSigner(params.TestChainConfig)

	for i := range txs {
		amount := big.NewInt(int64(i)*10 ^ 9)
		gas_price := big.NewInt(300_000)
		data := make([]byte, 100)
		// randomly assigned for debugging
		data[3] = 3
		data[4] = 3
		data[5] = 3
		data[6] = 3
		data[7] = 3
		tx := types.NewTransaction(uint64(i), common.Address{}, amount, 10*10^6, gas_price, data)
		signedTx, err := types.SignTx(tx, signer, key)
		if err != nil {
			panic(err)
		}
		txs[i] = signedTx
	}
	return txs
}

/*
transactionsStackTrieInsertionTemplate inserts n transactions into a stacktrie.
For each of the n modifications of the trie it asks for a proof - GetProof is called before
and after the modification. The transactions in the trie are not hashed and thus GetProof
does not require to query a database to get the preimages.

When the first transaction is added, a leaf is added to the trie
(it has index 1 which is used as a key when inserting into a trie, the key is changed by
calling KeybytesToHex(key) in TryUpdate to [0, 1, 16]).

When the second transaction is added (it has index 2, when inserting into a trie,
it gets changed to [0, 2, 16]), the extension node E is created with nibble 0 (note that
both leaves/transactions have the first nibble 0) and the underlying branch B with children
at positions 1 and 2 (second nibble of the two leaves).

At this point, the proof for the second transaction is (proofC when index = 2):
[226 16 160 212 52 159 164 192 63 244 122 229 5 208 58 20 16 54 62 169 98 62 238 163 88 174 155 252 118 132 91 148 62 122 23]
[248 81 128 160 32 244 75 78 180 11 251 73 229 254 70 16 254 170 54 254 200 97 231 24 180 34 220 244 153 76 1 194 23 63 64 224 160 46 141 2 37 188 204 110 232 46 31 230 82 226 213 98 71 18 241 37 90 213 167 221 58 33 36 249 248 180 207 235 47 128 128 128 128 128 128 128 128 128 128 128 128 128 128]
[248 200 2 131 4 147 224 131 1 226 65 148 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4 184 100 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 37 160 163 65 77 46 20 3 175 162 34 86 182 41 225 43 90 92 158 249 153 67 193 148 178 63 8 81 26 169 176 56 242 78 160 21 37 82 209 254 5 113 171 235 198 244 52 17 233 162 51 76 151 85 224 28 101 146 160 197 216 253 237 240 187 19 184]

Note that the first proof element is an extension node with nibble 0 = 16 - 16 (see
the second byte). The third byte (32 = 160 - 128) denotes the length of the subsequent stream
which represents the hash of the underlying branch.
The second proof element is the underlying branch. The second byte (81) denotes the length
of the subsequent RLP stream. The third byte (128) denotes the nil element at position 0.
Then there are two children at positions 1 (32 244 75...) and 2 (46 141 2...). Note that
these two 32-long value are the hashes of the two leaves/transactions in the branch.
The bytes 128 at the end of the branch RLP represents nil objects at positions 3 - 15.
The last proof element is the second transaction, for example the third nibble (2)
represents the index of the transaction.

When further 13 transactions are added, the branch B gets populated at positions 3 - 15
(the position 0 remains nil).

When the 16-th transaction is added (it has index 16, it gets changed to [1, 0, 16]),
the extension node E is turned into branch B1 which has children at positions 0 and 1.
At position 0 it has a branch B (which used to be the underlying branch of E1) and
at position 1 it has a leaf that represents the 16-transaction.

At this point, the proof for the second transaction is (proofC when index = 16):
[248 81 160 204 44 112 166 132 56 23 211 247 164 233 113 161 247 117 64 34 142 106 19 106 151 213 163 170 185 19 10 144 231 85 229 160 23 243 146 56 210 93 132 177 170 102 160 150 91 57 192 254 50 122 118 157 138 67 46 2 247 8 89 216 105 197 213 36 128 128 128 128 128 128 128 128 128 128 128 128 128 128 128]
[248 203 16 131 4 147 224 131 1 226 65 148 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 131 1 0 0 184 100 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 38 160 4 18 182 163 225 56 150 243 120 135 140 57 183 97 55 103 25 62 11 37 106 178 135 7 12 58 133 148 112 183 105 66 160 106 208 180 0 175 152 228 224 143 226 84 16 188 253 79 140 234 80 104 143 32 229 83 105 24 251 62 24 122 66 11 59]

The first proof element is a branch with children at position 0 (branch B) and 1 (newly added leaf).
The second element is the 16-th transaction. For example, the third byte (16) represents
the transaction index.
*/

func transactionsStackTrieInsertionTemplate(t *testing.T, n int) {
	txs := makeTransactions(n)
	db := rawdb.NewMemoryDatabase()
	stackTrie := trie.NewStackTrie(db)

	proofs, _ := stackTrie.UpdateAndGetProofs(db, types.Transactions(txs))

	rlp_last_tx, _ := txs[n-1].MarshalBinary()
	last_proofC := proofs[len(proofs)-1].GetProofC()

	tx_len := len(txs)
	proof_len := len(proofs)

	// Proof of the first tx is appended at the end of the proofs if len(tx) < 0x80
	// That's why we minus 2 here.
	if tx_len > 1 && tx_len < 128 {
		last_proofC = proofs[proof_len-2].GetProofC()
	}
	last_leaf_proof := last_proofC[len(last_proofC)-1]

	if tx_len != proof_len {
		fmt.Println("Expected to have", tx_len, ", but only got", proof_len)
		t.Fail()
	}

	if !bytes.Equal(last_leaf_proof, rlp_last_tx) {
		fmt.Println("- last_tx\n  ", rlp_last_tx)
		fmt.Println("- last_proof\n  ", last_leaf_proof)
		t.Fail()
	}
}

func TestStackTrieInsertion_1Tx(t *testing.T) {
	// Only one leaf
	transactionsStackTrieInsertionTemplate(t, 1)
}

func TestStackTrieInsertion_2Txs(t *testing.T) {
	// One ext. node and one leaf
	transactionsStackTrieInsertionTemplate(t, 2)
}

func TestStackTrieInsertion_3Txs(t *testing.T) {
	// One ext. node, one branch and one leaf
	transactionsStackTrieInsertionTemplate(t, 3)
}

func TestStackTrieInsertion_4Txs(t *testing.T) {
	// One ext. node, one branch and two leaves
	transactionsStackTrieInsertionTemplate(t, 4)
}

func TestStackTrieInsertion_16Txs(t *testing.T) {
	// One ext. node and one branch with full leaves (16 leaves)
	transactionsStackTrieInsertionTemplate(t, 16)
}

func TestStackTrieInsertion_17Txs(t *testing.T) {
	// One ext. node, 3 branches and 17 leaves.
	// The original ext. node turns into a branch (B1) which has children at position 0 and 1.
	// At position 0 of B1, it has a branch with full leaves
	// At position 1 of B1, it has a newly leaf
	transactionsStackTrieInsertionTemplate(t, 17)
}

func TestStackTrieInsertion_33Txs(t *testing.T) {
	// Follow above test and have one more branch generated
	transactionsStackTrieInsertionTemplate(t, 33)
}

func TestStackTrieInsertion_129Txs(t *testing.T) {
	// The first tx (index 0) is inserted into position 8 of the branch of the first layer
	// Th 129th tx is the neighbor of the first tx
	transactionsStackTrieInsertionTemplate(t, 129)
}

func TestStackTrieInsertion_ManyTxs(t *testing.T) {
	// Just randomly picking a large number.
	// The cap of block gas limit is 30M, the minimum gas cost of a tx is 21k
	// 30M / 21k ~= 1429
	transactionsStackTrieInsertionTemplate(t, 2000)
}

/*
batchedTransactionsStackTrieProofTemplate inserts n transactions into a stacktrie,
the trie is then hashed (DeriveSha call).
The proof is asked for one of the n transactions. The transactions in the trie are hashed and thus
GetProof requires to query a database to get the preimages.
*/
func batchedTransactionsStackTrieProofTemplate(n int) {
	txs := makeTransactions(n)
	db := rawdb.NewMemoryDatabase()
	stackTrie := trie.NewStackTrie(db)

	// Update the trie with transactions:
	types.DeriveSha(types.Transactions(txs), stackTrie)

	var indexBuf []byte
	indexBuf = rlp.AppendUint64(indexBuf[:0], uint64(1))

	proofS, _, _, err := stackTrie.GetProof(db, indexBuf)
	if err != nil {
		fmt.Println(err)
		return
	}

	fmt.Println("proofS", proofS)
	fmt.Println("===")
}

func TestBatchedTxsProof_1Tx(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(1)
}

func TestBatchedTxsProof_2Txs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(2)
}

func TestBatchedTxsProof_3Txs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(3)
}
func TestBatchedTxsProof_4Txs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(4)
}

func TestBatchedTxsProof_16Txs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(16)
}

func TestBatchedTxsProof_17Txs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(17)
}
func TestBatchedTxsProof_33Txs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(33)
}
func TestBatchedTxsProof_ManyTxs(t *testing.T) {
	batchedTransactionsStackTrieProofTemplate(2000)
}

//
// Generate witness and store to json files
//

// witnessGenerationTemplate obtains the GetProof proof before and after the modification for each
// of the modification. It then converts the two proofs into an MPT circuit witness for each of
// the modifications.
func witnessGenerationTemplate(testName string, list types.DerivableList, loopAll bool) []Node {
	db := rawdb.NewMemoryDatabase()
	stackTrie := trie.NewStackTrie(db)
	proofs, _ := stackTrie.UpdateAndGetProofs(db, list)
	root, _ := stackTrie.Commit()

	var nodes []Node
	var genWitness = func(idx int, proof *trie.StackProof) {
		var key []byte
		var subNodes []Node
		subNodes = append(subNodes, GetStartNode(testName, common.Hash{}, root, 0))
		var node []Node
		if (idx <= 0x80 && len(proofs) == idx) || idx == 128 {
			key := rlp.AppendUint64(key[:0], uint64(0))
			node = GenerateWitness(uint(0), key, key, proof)
		} else {
			key := rlp.AppendUint64(key[:0], uint64(idx))
			node = GenerateWitness(uint(idx), key, key, proof)
		}
		subNodes = append(subNodes, node...)
		subNodes = append(subNodes, GetEndNode())

		nodes = append(nodes, subNodes...)
		verifyNodeNumber(subNodes, *proof)
	}

	if loopAll {
		for i, proof := range proofs {
			genWitness(i+1, &proof)
		}
	} else {
		i := len(proofs) - 1
		if len(proofs) <= 128 {
			// When the number of txs is less than 128, the last proof is the proof of tx0
			// and we want the last proof (not the proof of tx0).
			// That's why we minus 2 here
			i = len(proofs) - 2
			genWitness(i+1, &proofs[i])
		} else {
			genWitness(i, &proofs[i])
		}
	}
	return nodes
}

// A quick and naive way to verify nodes number, might not be accurate
func verifyNodeNumber(nodes []Node, proof trie.StackProof) {
	// start and end nodes
	nodeNum := len(nodes) - 2

	proofS := proof.GetProofS()
	proofC := proof.GetProofC()
	len1 := len(proofS)
	len2 := len(proofC)
	maxLen := max(len1, len2)
	minLen := min(len1, len2)

	typesS := proof.GetTypeS()
	typesC := proof.GetTypeC()
	var cntExtS, cntExtC int
	for _, t := range typesS {
		if t == trie.ExtNode {
			cntExtS++
		}
	}
	for _, t := range typesC {
		if t == trie.ExtNode {
			cntExtC++
		}
	}
	maxExtCnt := max(cntExtS, cntExtC)

	// Most of cases
	if maxLen == minLen+1 {
		// ext. node won't have a node, it shares with a branch
		if nodeNum != maxLen-maxExtCnt {
			fmt.Println("WARNING: node number not matched: nodeNum != maxLen")
		}
	} else if maxLen == minLen {
		typeS := proof.GetTypeS()
		typeC := proof.GetTypeC()

		// [EXT - BRANCH] -> [BRANCH - LEAF]
		if typeS[0] != typeC[0] {
			if nodeNum == maxLen+1 {
				fmt.Println("WARNING: node number not matched: typeS[0] != typeC[0] && nodeNum == maxLen+1")
			}
		} else {
			if nodeNum != maxLen {
				fmt.Println("WARNING: node number not matched: nodeNum != maxLen")
			}
		}
	} else if maxLen > minLen+1 {
		// usually it happens when a new ext. node created
		// [BRANCH - BRANCH - LEAF] -> [BRANCH - BRANCH - EXT - BRANCH - LEAF]
		if nodeNum == maxLen+1 {
			fmt.Println("WARNING: node number not matched: typeS[0] != typeC[0] && nodeNum == maxLen+1")
		}
	} else {
		fmt.Println("WARNING: WHERE AM I??")
	}
}

func TestTransactionsModExtNodes(t *testing.T) {
	t.Skip("Not working now.")
	// randomly pick 5 mod-ext nodes
	txs := makeTransactions(2000)
	var nodes []Node
	nodes = witnessGenerationTemplate("TransactionModeExt_16", types.Transactions(txs[:16]), false)
	nodes = append(nodes, witnessGenerationTemplate("TransactionModeExt_144", types.Transactions(txs[:145]), false)...)
	nodes = append(nodes, witnessGenerationTemplate("TransactionModeExt_512", types.Transactions(txs[:513]), false)...)
	nodes = append(nodes, witnessGenerationTemplate("TransactionModeExt_1552", types.Transactions(txs[:1553]), false)...)
	nodes = append(nodes, witnessGenerationTemplate("TransactionModeExt_1808", types.Transactions(txs[:1809]), false)...)

	StoreNodes("TransactionsModExtNodes", nodes)
}

func TestTransactionsNum256(t *testing.T) {
	txs := makeTransactions(256)
	nodes := witnessGenerationTemplate("TransactionsNum256", types.Transactions(txs), true)
	StoreNodes("TransactionsNum256", nodes)
}

func TestSingleTransactionNum1(t *testing.T) {
	// A. [] --> [LEAF]
	txs := makeTransactions(1)
	nodes := witnessGenerationTemplate("SingleTransactionNum1", types.Transactions(txs), true)
	StoreNodes("SingleTransactionNum1", nodes)
}

func TestSingleTransactionNum3(t *testing.T) {
	// B. [LEAF] --> [EXT - BRANCH - LEAF]
	txs := makeTransactions(3)
	nodes := witnessGenerationTemplate("SingleTransactionNum3", types.Transactions(txs), false)
	StoreNodes("SingleTransactionNum3", nodes)
}

func TestSingleTransactionNormal(t *testing.T) {
	// C. [EXT - BRANCH] --> [EXT - BRANCH - LEAF]
	txs := makeTransactions(5)
	nodes := witnessGenerationTemplate("SingleTransactionNormal", types.Transactions(txs), false)
	StoreNodes("SingleTransactionNormal", nodes)
}

func TestSingleTransactionNormal2(t *testing.T) {
	// C. [EXT - BRANCH] --> [EXT - BRANCH - LEAF]
	// randomly pick a large number of tx
	txs := makeTransactions(1500)
	nodes := witnessGenerationTemplate("SingleTransactionNormal", types.Transactions(txs), false)
	StoreNodes("SingleTransactionNormal", nodes)
}

func TestSingleTransactionEndLeaf(t *testing.T) {
	// D. [BRANCH - BRANCH] --> [BRANCH - BRANCH - LEAF]
	txs := makeTransactions(129)
	nodes := witnessGenerationTemplate("SingleTransactionEndLeaf", types.Transactions(txs), false)
	StoreNodes("SingleTransactionEndLeaf", nodes)
}

func TestSingleTransactionNewExtBraLeaf(t *testing.T) {
	// E. [BRANCH - BRANCH - LEAF] --> [BRANCH - BRANCH - EXT - BRANCH - LEAF]
	txs := makeTransactions(130)
	nodes := witnessGenerationTemplate("SingleTransactionNewExtBraLeaf", types.Transactions(txs), false)
	StoreNodes("SingleTransactionNewExtBraLeaf", nodes)
}
