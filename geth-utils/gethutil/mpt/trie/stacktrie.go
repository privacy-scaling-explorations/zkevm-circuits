// Copyright 2020 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package trie

import (
	"bufio"
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"io"
	"main/gethutil/mpt/types"
	"slices"
	"sync"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/log"

	//"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/rlp"
)

var ErrCommitDisabled = errors.New("no database for committing")

var stPool = sync.Pool{
	New: func() interface{} {
		return NewStackTrie(nil)
	},
}

func stackTrieFromPool(db ethdb.KeyValueWriter) *StackTrie {
	st := stPool.Get().(*StackTrie)
	st.db = db
	return st
}

func returnToPool(st *StackTrie) {
	st.Reset()
	stPool.Put(st)
}

// StackTrie is a trie implementation that expects keys to be inserted
// in order. Once it determines that a subtree will no longer be inserted
// into, it will hash it and free up the memory it uses.
type StackTrie struct {
	nodeType  uint8                // node type (as in branch, ext, leaf)
	val       []byte               // value contained by this node if it's a leaf
	key       []byte               // key chunk covered by this (full|ext) node
	keyOffset int                  // offset of the key chunk inside a full key
	children  [16]*StackTrie       // list of children (for fullnodes and exts)
	db        ethdb.KeyValueWriter // Pointer to the commit db, can be nil
}

// NewStackTrie allocates and initializes an empty trie.
func NewStackTrie(db ethdb.KeyValueWriter) *StackTrie {
	return &StackTrie{
		nodeType: EmptyNode,
		db:       db,
	}
}

// NewFromBinary initialises a serialized stacktrie with the given db.
func NewFromBinary(data []byte, db ethdb.KeyValueWriter) (*StackTrie, error) {
	var st StackTrie
	if err := st.UnmarshalBinary(data); err != nil {
		return nil, err
	}
	// If a database is used, we need to recursively add it to every child
	if db != nil {
		st.setDb(db)
	}
	return &st, nil
}

// MarshalBinary implements encoding.BinaryMarshaler
func (st *StackTrie) MarshalBinary() (data []byte, err error) {
	var (
		b bytes.Buffer
		w = bufio.NewWriter(&b)
	)
	if err := gob.NewEncoder(w).Encode(struct {
		Nodetype  uint8
		Val       []byte
		Key       []byte
		KeyOffset uint8
	}{
		st.nodeType,
		st.val,
		st.key,
		uint8(st.keyOffset),
	}); err != nil {
		return nil, err
	}
	for _, child := range st.children {
		if child == nil {
			w.WriteByte(0)
			continue
		}
		w.WriteByte(1)
		if childData, err := child.MarshalBinary(); err != nil {
			return nil, err
		} else {
			w.Write(childData)
		}
	}
	w.Flush()
	return b.Bytes(), nil
}

// UnmarshalBinary implements encoding.BinaryUnmarshaler
func (st *StackTrie) UnmarshalBinary(data []byte) error {
	r := bytes.NewReader(data)
	return st.unmarshalBinary(r)
}

func (st *StackTrie) unmarshalBinary(r io.Reader) error {
	var dec struct {
		Nodetype  uint8
		Val       []byte
		Key       []byte
		KeyOffset uint8
	}
	gob.NewDecoder(r).Decode(&dec)
	st.nodeType = dec.Nodetype
	st.val = dec.Val
	st.key = dec.Key
	st.keyOffset = int(dec.KeyOffset)

	var hasChild = make([]byte, 1)
	for i := range st.children {
		if _, err := r.Read(hasChild); err != nil {
			return err
		} else if hasChild[0] == 0 {
			continue
		}
		var child StackTrie
		child.unmarshalBinary(r)
		st.children[i] = &child
	}
	return nil
}

func (st *StackTrie) setDb(db ethdb.KeyValueWriter) {
	st.db = db
	for _, child := range st.children {
		if child != nil {
			child.setDb(db)
		}
	}
}

func newLeaf(ko int, key, val []byte, db ethdb.KeyValueWriter) *StackTrie {
	st := stackTrieFromPool(db)
	st.nodeType = LeafNode
	st.keyOffset = ko
	st.key = append(st.key, key[ko:]...)
	st.val = val
	return st
}

func newExt(ko int, key []byte, child *StackTrie, db ethdb.KeyValueWriter) *StackTrie {
	st := stackTrieFromPool(db)
	st.nodeType = ExtNode
	st.keyOffset = ko
	st.key = append(st.key, key[ko:]...)
	st.children[0] = child
	return st
}

// List all values that StackTrie#nodeType can hold
const (
	EmptyNode = iota
	BranchNode
	ExtNode
	LeafNode
	HashedNode
)

// TryUpdate inserts a (key, value) pair into the stack trie
func (st *StackTrie) TryUpdate(key, value []byte) error {
	k := KeybytesToHex(key)
	if len(value) == 0 {
		panic("deletion not supported")
	}
	st.insert(k[:len(k)-1], value)
	return nil
}

func (st *StackTrie) Update(key, value []byte) {
	if err := st.TryUpdate(key, value); err != nil {
		log.Error(fmt.Sprintf("Unhandled trie error: %v", err))
	}
}

func (st *StackTrie) Reset() {
	//st.db = nil
	st.key = st.key[:0]
	st.val = nil
	for i := range st.children {
		st.children[i] = nil
	}
	st.nodeType = EmptyNode
	st.keyOffset = 0
}

// Helper function that, given a full key, determines the index
// at which the chunk pointed by st.keyOffset is different from
// the same chunk in the full key.
func (st *StackTrie) getDiffIndex(key []byte) int {
	diffindex := 0
	for ; diffindex < len(st.key) && st.key[diffindex] == key[st.keyOffset+diffindex]; diffindex++ {
	}
	return diffindex
}

// Helper function to that inserts a (key, value) pair into
// the trie.
// https://github.dev/ethereum/go-ethereum/blob/00905f7dc406cfb67f64cd74113777044fb886d8/core/types/hashing.go#L105-L134
func (st *StackTrie) insert(key, value []byte) {
	switch st.nodeType {
	case BranchNode: /* Branch */
		idx := int(key[st.keyOffset])
		// Unresolve elder siblings
		for i := idx - 1; i >= 0; i-- {
			if st.children[i] != nil {
				if st.children[i].nodeType != HashedNode {
					st.children[i].hash(true)
				}
				break
			}
		}

		// Add new child
		if st.children[idx] == nil {
			st.children[idx] = newLeaf(st.keyOffset+1, key, value, st.db)
		} else {
			st.children[idx].insert(key, value)
		}

	case ExtNode: /* Ext */
		// Compare both key chunks and see where they differ
		diffidx := st.getDiffIndex(key)
		// Check if chunks are identical. If so, recurse into
		// the child node. Otherwise, the key has to be split
		// into 1) an optional common prefix, 2) the fullnode
		// representing the two differing path, and 3) a leaf
		// for each of the differentiated subtrees.
		if diffidx == len(st.key) {
			// Ext key and key segment are identical, recurse into
			// the child node.
			st.children[0].insert(key, value)
			return
		}
		// Save the original part. Depending if the break is
		// at the extension's last byte or not, create an
		// intermediate extension or use the extension's child
		// node directly.
		var n *StackTrie
		if diffidx < len(st.key)-1 {
			n = newExt(diffidx+1, st.key, st.children[0], st.db)
		} else {
			// Break on the last byte, no need to insert
			// an extension node: reuse the current node
			n = st.children[0]
		}
		// Convert to hash
		n.hash(true)
		var p *StackTrie
		if diffidx == 0 {
			// the break is on the first byte, so
			// the current node is converted into
			// a branch node.
			st.children[0] = nil
			p = st
			st.nodeType = BranchNode
		} else {
			// the common prefix is at least one byte
			// long, insert a new intermediate branch
			// node.
			st.children[0] = stackTrieFromPool(st.db)
			st.children[0].nodeType = BranchNode
			st.children[0].keyOffset = st.keyOffset + diffidx
			p = st.children[0]
		}
		// Create a leaf for the inserted part
		o := newLeaf(st.keyOffset+diffidx+1, key, value, st.db)

		// Insert both child leaves where they belong:
		origIdx := st.key[diffidx]
		newIdx := key[diffidx+st.keyOffset]
		p.children[origIdx] = n
		p.children[newIdx] = o
		st.key = st.key[:diffidx]

	case LeafNode: /* Leaf */
		// Compare both key chunks and see where they differ
		diffidx := st.getDiffIndex(key)

		// Overwriting a key isn't supported, which means that
		// the current leaf is expected to be split into 1) an
		// optional extension for the common prefix of these 2
		// keys, 2) a fullnode selecting the path on which the
		// keys differ, and 3) one leaf for the differentiated
		// component of each key.
		if diffidx >= len(st.key) {
			panic("Trying to insert into existing key")
		}

		// Check if the split occurs at the first nibble of the
		// chunk. In that case, no prefix extnode is necessary.
		// Otherwise, create that
		var p *StackTrie
		if diffidx == 0 {
			// Convert current leaf into a branch
			st.nodeType = BranchNode
			p = st
			st.children[0] = nil
		} else {
			// Convert current node into an ext,
			// and insert a child branch node.
			st.nodeType = ExtNode
			st.children[0] = NewStackTrie(st.db)
			st.children[0].nodeType = BranchNode
			st.children[0].keyOffset = st.keyOffset + diffidx
			p = st.children[0]
		}

		// Create the two child leaves: the one containing the
		// original value and the one containing the new value
		// The child leave will be hashed directly in order to
		// free up some memory.
		origIdx := st.key[diffidx]
		p.children[origIdx] = newLeaf(diffidx+1, st.key, st.val, st.db)
		p.children[origIdx].hash(true)

		newIdx := key[diffidx+st.keyOffset]
		p.children[newIdx] = newLeaf(p.keyOffset+1, key, value, st.db)

		// Finally, cut off the key part that has been passed
		// over to the children.
		st.key = st.key[:diffidx]
		st.val = nil
	case EmptyNode: /* Empty */
		st.nodeType = LeafNode
		st.key = key[st.keyOffset:]
		st.val = value
	case HashedNode:
		panic("trying to insert into hash")
	default:
		panic("invalid type")
	}
}

func (st *StackTrie) branchToHasher(doUpdate bool) *hasher {
	if st.nodeType != BranchNode {
		panic("Converting branch to RLP: wrong node")
	}
	var nodes [17]Node
	for i, child := range st.children {
		if child == nil {
			nodes[i] = nilValueNode
			continue
		}
		child.hash(doUpdate)
		if len(child.val) < 32 {
			nodes[i] = rawNode(child.val)
		} else {
			nodes[i] = HashNode(child.val)
		}
		if doUpdate {
			st.children[i] = nil // Reclaim mem from subtree
			returnToPool(child)
		}
	}
	nodes[16] = nilValueNode

	h := NewHasher(false)
	defer returnHasherToPool(h)
	h.tmp.Reset()
	if err := rlp.Encode(&h.tmp, nodes); err != nil {
		panic(err)
	}

	// h.tmp is branch RLP
	return h
}

func (st *StackTrie) extNodeToHasher(doUpdate bool) *hasher {
	if st.nodeType != ExtNode {
		panic("Converting extension node to RLP: wrong node")
	}
	st.children[0].hash(doUpdate)
	h := NewHasher(false)
	defer returnHasherToPool(h)
	h.tmp.Reset()
	var valuenode Node
	if len(st.children[0].val) < 32 {
		valuenode = rawNode(st.children[0].val)
	} else {
		valuenode = HashNode(st.children[0].val)
	}
	n := struct {
		Key []byte
		Val Node
	}{
		Key: HexToCompact(st.key),
		Val: valuenode,
	}
	if err := rlp.Encode(&h.tmp, n); err != nil {
		panic(err)
	}
	if doUpdate {
		returnToPool(st.children[0])
		st.children[0] = nil // Reclaim mem from subtree
	}

	// h.tmp is extension node RLP
	return h
}

// hash() hashes the node 'st' and converts it into 'HashedNode', if possible.
// Possible outcomes:
// 1. The rlp-encoded value was >= 32 bytes:
//   - Then the 32-byte `hash` will be accessible in `st.val`.
//   - And the 'st.type' will be 'HashedNode'
//
// 2. The rlp-encoded value was < 32 bytes
//   - Then the <32 byte rlp-encoded value will be accessible in 'st.val'.
//   - And the 'st.type' will be 'HashedNode' AGAIN
//
// This method will also:
// set 'st.type' to HashedNode
// clear 'st.key'
func (st *StackTrie) hash(doUpdate bool) {
	/* Shortcut if node is already hashed */
	if st.nodeType == HashedNode {
		return
	}
	// The 'hasher' is taken from a pool, but we don't actually
	// claim an instance until all children are done with their hashing,
	// and we actually need one
	var h *hasher

	switch st.nodeType {
	case BranchNode:
		h = st.branchToHasher(doUpdate)
	case ExtNode:
		h = st.extNodeToHasher(doUpdate)
	case LeafNode:
		h = NewHasher(false)
		defer returnHasherToPool(h)
		h.tmp.Reset()

		k := make([]byte, len(st.key))
		copy(k, st.key)
		k = append(k, byte(16))

		if doUpdate {
			st.key = k
		}
		sz := hexToCompactInPlace(k)
		n := [][]byte{k[:sz], st.val}
		if err := rlp.Encode(&h.tmp, n); err != nil {
			panic(err)
		}
	case EmptyNode:
		st.val = emptyRoot.Bytes()
		st.key = st.key[:0]
		st.nodeType = HashedNode
		return
	default:
		panic("Invalid node type")
	}
	if doUpdate {
		st.key = st.key[:0]
		st.nodeType = HashedNode
	}
	if len(h.tmp) < 32 {
		st.val = common.CopyBytes(h.tmp)
		return
	}
	// Write the hash to the 'val'. We allocate a new val here to not mutate
	// input values
	st.val = make([]byte, 32)
	h.sha.Reset()
	h.sha.Write(h.tmp)
	h.sha.Read(st.val)
	if st.db != nil {
		// TODO! Is it safe to Put the slice here?
		// Do all db implementations copy the value provided?
		st.db.Put(st.val, h.tmp)
	}
}

// Hash returns the hash of the current node
func (st *StackTrie) Hash() (h common.Hash) {
	st.hash(true)
	if len(st.val) != 32 {
		// If the node's RLP isn't 32 bytes long, the node will not
		// be hashed, and instead contain the  rlp-encoding of the
		// node. For the top level node, we need to force the hashing.
		ret := make([]byte, 32)
		h := NewHasher(false)
		defer returnHasherToPool(h)
		h.sha.Reset()
		h.sha.Write(st.val)
		h.sha.Read(ret)
		return common.BytesToHash(ret)
	}
	return common.BytesToHash(st.val)
}

// Commit will firstly hash the entry trie if it's still not hashed
// and then commit all nodes to the associated database. Actually most
// of the trie nodes MAY have been committed already. The main purpose
// here is to commit the root node.
//
// The associated database is expected, otherwise the whole commit
// functionality should be disabled.
func (st *StackTrie) Commit() (common.Hash, error) {
	if st.db == nil {
		return common.Hash{}, ErrCommitDisabled
	}
	st.hash(true)
	if len(st.val) != 32 {
		// If the node's RLP isn't 32 bytes long, the node will not
		// be hashed (and committed), and instead contain the  rlp-encoding of the
		// node. For the top level node, we need to force the hashing+commit.
		ret := make([]byte, 32)
		h := NewHasher(false)
		defer returnHasherToPool(h)
		h.sha.Reset()
		h.sha.Write(st.val)
		h.sha.Read(ret)
		st.db.Put(ret, st.val)
		return common.BytesToHash(ret), nil
	}
	return common.BytesToHash(st.val), nil
}

const RLP_SHORT_STR_FLAG = 128
const RLP_SHORT_LIST_FLAG = 192
const RLP_LONG_LIST_FLAG = 248
const LEN_OF_HASH = 32

// Note:
// In RLP encoding, if the value is between [0x80, 0xb7] ([128, 183]),
// it means following data is a short string (0 - 55bytes).
// Which implies if the value is 128, it's an empty string.
func (st *StackTrie) getNodeFromBranchRLP(branch []byte, idx int) []byte {

	start := int(branch[0])
	start_idx := 0
	if start >= RLP_SHORT_LIST_FLAG && start < RLP_LONG_LIST_FLAG {
		// In RLP encoding, length in the range of [192 248] is a short list.
		// In stack trie, it usually means an extension node and the first byte is nibble
		// and that's why we start from 2
		start_idx = 2
	} else if start >= RLP_LONG_LIST_FLAG {
		// In RLP encoding, length in the range of [248 ~ ] is a long list.
		// The RLP byte minus 248 (branch[0] - 248) is the length in bytes of the length of the payload
		// and the payload is right after the length.
		// That's why we add 2 here
		// e.g. [248 81 128 160 ...]
		// `81` is the length of the payload and payload starts from `128`
		start_idx = start - RLP_LONG_LIST_FLAG + 2
	}

	// If 1st node is neither 128(empty node) nor 160, it should be a leaf
	b := int(branch[start_idx])
	if b != RLP_SHORT_STR_FLAG && b != (RLP_SHORT_STR_FLAG+LEN_OF_HASH) {
		return []byte{0}
	}

	current_idx := 0
	for i := start_idx; i < len(branch); i++ {
		b = int(branch[i])
		switch b {
		case RLP_SHORT_STR_FLAG: // 128
			// if the current index is we're looking for, return an empty node directly
			if current_idx == idx {
				return []byte{128}
			}
			current_idx++
		case RLP_SHORT_STR_FLAG + LEN_OF_HASH: // 160
			if current_idx == idx {
				return branch[i+1 : i+1+LEN_OF_HASH]
			}
			// jump to next encoded element
			i += LEN_OF_HASH
			current_idx++
		default:
			if b >= 192 && b < 248 {
				length := b - 192
				if current_idx == idx {
					return branch[i+1 : i+1+length]
				}
				i += length
				current_idx++
			}
		}
	}

	return []byte{0}
}

type StackProof struct {
	proofS     [][]byte
	proofC     [][]byte
	nibblesS   [][]byte
	nibblesC   [][]byte
	proofSType []uint8
	proofCType []uint8
}

func (sp *StackProof) GetProofS() [][]byte {
	return sp.proofS
}

func (sp *StackProof) GetProofC() [][]byte {
	return sp.proofC
}
func (sp *StackProof) GetNibblesS() [][]byte {
	return sp.nibblesS
}
func (sp *StackProof) GetNibblesC() [][]byte {
	return sp.nibblesC
}

func (sp *StackProof) GetTypeS() []byte {
	return sp.proofSType
}
func (sp *StackProof) GetTypeC() []byte {
	return sp.proofCType
}

func isBranch(proofEl []byte) bool {
	elems, _, _ := rlp.SplitList(proofEl)
	c, _ := rlp.CountValues(elems)
	return c == 17
}

func printProof(ps [][]byte, t, idx []byte) {
	fmt.Print(" [")
	for i, _ := range ps {
		if t[i] == ExtNode {
			fmt.Print("EXT - ")
		} else if t[i] == BranchNode {
			fmt.Print("BRANCH - ")
		} else if t[i] == LeafNode {
			fmt.Print("LEAF - ")
		} else if t[i] == HashedNode {
			fmt.Print("HASHED - ")
		} else {
			fmt.Print("NOT SUPPORT NOW!!")
		}
	}
	fmt.Println("]")

}

func (st *StackTrie) UpdateAndGetProof(db ethdb.KeyValueReader, indexBuf, value []byte) (StackProof, error) {
	proofS, nibblesS, typesS, err := st.GetProof(db, indexBuf)
	if err != nil {
		return StackProof{}, err
	}
	// printProof(proofS, typesS, indexBuf)

	st.Update(indexBuf, value)

	proofC, nibblesC, typesC, err := st.GetProof(db, indexBuf)
	if err != nil {
		return StackProof{}, err
	}
	// printProof(proofC, typesC, indexBuf)

	return StackProof{proofS, proofC, nibblesS, nibblesC, typesS, typesC}, nil
}

// We refer to the link below for this function.
// https://github.com/ethereum/go-ethereum/blob/00905f7dc406cfb67f64cd74113777044fb886d8/core/types/hashing.go#L105-L134
func (st *StackTrie) UpdateAndGetProofs(db ethdb.KeyValueReader, list types.DerivableList) ([]StackProof, error) {
	valueBuf := types.EncodeBufferPool.Get().(*bytes.Buffer)
	defer types.EncodeBufferPool.Put(valueBuf)

	var proofs []StackProof

	// StackTrie requires values to be inserted in increasing hash order, which is not the
	// order that `list` provides hashes in. This insertion sequence ensures that the
	// order is correct.
	var indexBuf []byte
	for i := 1; i < list.Len() && i <= 0x7f; i++ {
		indexBuf = rlp.AppendUint64(indexBuf[:0], uint64(i))
		value := types.EncodeForDerive(list, i, valueBuf)
		proof, err := st.UpdateAndGetProof(db, indexBuf, value)
		if err != nil {
			return nil, err
		}
		proofs = append(proofs, proof)
	}

	// special case when index is 0
	// rlp.AppendUint64() encodes index 0 to [128]
	if list.Len() > 0 {
		indexBuf = rlp.AppendUint64(indexBuf[:0], 0)
		value := types.EncodeForDerive(list, 0, valueBuf)
		proof, err := st.UpdateAndGetProof(db, indexBuf, value)
		if err != nil {
			return nil, err
		}
		proofs = append(proofs, proof)
	}

	for i := 0x80; i < list.Len(); i++ {
		indexBuf = rlp.AppendUint64(indexBuf[:0], uint64(i))
		value := types.EncodeForDerive(list, i, valueBuf)
		proof, err := st.UpdateAndGetProof(db, indexBuf, value)
		if err != nil {
			return nil, err
		}
		proofs = append(proofs, proof)
	}

	return proofs, nil
}

func (st *StackTrie) GetProof(db ethdb.KeyValueReader, key []byte) ([][]byte, [][]byte, []uint8, error) {
	k := KeybytesToHex(key)
	if st.nodeType == EmptyNode {
		return [][]byte{}, nil, []uint8{EmptyNode}, nil
	}

	// Note that when root is a leaf, this leaf should be returned even if you ask for a different key (than the key of
	// of this leaf) - this is how it works in state GetProof and how it should, because this means the second change
	// of the trie. The first change is going from empty trie to the trie with only a leaf. The second change is going
	// from a leaf to a branch (or extension node). That means the second change requires a placeholder branch
	// and when there is a placeholder branch, the circuit checks that there are only two leaves in a branch and one
	// (the one not just added) is the same as in the S proof. This wouldn't work if we would have a placeholder leaf
	// in the S proof (another reason is that the S proof with a placeholder leaf would be an empty trie and thus with
	// a root of an empty trie - which is not the case in S proof).
	if st.nodeType == LeafNode {
		return [][]byte{st.val}, nil, []uint8{LeafNode}, nil
	}

	var nibbles [][]byte
	var proofType []uint8
	var proof [][]byte
	var nodes []*StackTrie
	c := st

	for i := 0; i < len(k); i++ {
		proofType = append(proofType, c.nodeType)
		if c.nodeType == ExtNode {
			i += len(c.key) - 1
			nodes = append(nodes, c)
			c = c.children[0]
		} else if c.nodeType == BranchNode {
			nodes = append(nodes, c)
			c = c.children[k[i]]
			if c == nil {
				break
			}
		} else if c.nodeType == LeafNode {
			nodes = append(nodes, c)
			break
		} else if c.nodeType == HashedNode {
			c_rlp, error := db.Get(c.val)
			if error != nil {
				panic(error)
			}
			proof = append(proof, c_rlp)
			nibbles = append(nibbles, c.key)
			branchChild := st.getNodeFromBranchRLP(c_rlp, int(k[i]))
			// branchChild is of length 1 when there is no child at this position in the branch
			// (`branchChild = [128]` in this case), but it is also of length 1 when `c_rlp` is a leaf.
			if len(branchChild) == 1 && (branchChild[0] == 128 || branchChild[0] == 0) {
				// no child at this position (128 is RLP encoding for nil object)
				break
			}
			c.val = branchChild
			// if there are children, the node type should be branch
			proofType[len(proofType)-1] = BranchNode
		}
	}

	// Differently as in the Trie, the StackTrie branch doesn't store children once it is hashed.
	// For getting the proof, we need to hash the nodes, but once they are hashed we cannot add children
	// to them - which is needed in MPT proof, because we need a proof for each modification (after
	// the first modification, some nodes are hashed and we cannot add children to the hashed node).

	lNodes := len(nodes)
	for i := lNodes - 1; i >= 0; i-- {
		node := nodes[i]
		if node.nodeType == LeafNode {
			nibbles = append(nibbles, []byte{})
			rlp, error := db.Get(node.val)
			if error != nil { // TODO: avoid error when RLP
				proof = append(proof, node.val) // already have RLP
			} else {
				proof = append(proof, rlp)
			}
		} else if node.nodeType == BranchNode || node.nodeType == ExtNode {
			node.hash(false)

			raw_rlp, error := db.Get(node.val)
			if error != nil {
				return nil, nil, nil, error
			}
			proof = append(proof, raw_rlp)
			if node.nodeType == ExtNode {

				rlp_flag := uint(raw_rlp[0])
				if rlp_flag < 192 || rlp_flag >= 248 {
					panic("should not happen!")
				}
				nibbles = append(nibbles, node.key)
			} else {
				nibbles = append(nibbles, []byte{})
			}
		}

	}
	// The proof is now reversed (only for non-hashed),
	// let's reverse it back to have the leaf at the bottom:
	slices.Reverse(proof)
	slices.Reverse(nibbles)
	// }

	return proof, nibbles, proofType, nil
}
