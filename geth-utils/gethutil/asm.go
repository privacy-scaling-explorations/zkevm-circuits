package gethutil

import (
	"fmt"
	"io"
	"math/big"

	"github.com/ethereum/go-ethereum/core/vm"
)

type asm struct {
	Bytecode         []byte
	labelMap         map[string]int
	pendingLabelsMap map[string][]int
}

func NewAssembly() *asm {
	return &asm{
		labelMap:         make(map[string]int),
		pendingLabelsMap: make(map[string][]int),
	}
}

func (a *asm) PrintMnemonics(out io.Writer) {
	for idx := 0; idx < len(a.Bytecode); {
		code := vm.OpCode(a.Bytecode[idx])
		if code.IsPush() {
			n := int(code) - int(vm.PUSH1) + 1
			fmt.Fprintf(out, "%02d\t%s\t0x%x\n", idx, code.String(), a.Bytecode[idx+1:idx+1+n])
			idx += n + 1
		} else {
			fmt.Fprintf(out, "%02d\t%s\n", idx, code.String())
			idx++
		}
	}
}

// 0x0 range
func (a *asm) Stop() *asm                       { return a.appendByte(vm.STOP) }
func (a *asm) Add(v ...interface{}) *asm        { return a.opWithPush(vm.ADD, v...) }
func (a *asm) Mul(v ...interface{}) *asm        { return a.opWithPush(vm.MUL, v...) }
func (a *asm) Sub(v ...interface{}) *asm        { return a.opWithPush(vm.SUB, v...) }
func (a *asm) Div(v ...interface{}) *asm        { return a.opWithPush(vm.DIV, v...) }
func (a *asm) SDiv(v ...interface{}) *asm       { return a.opWithPush(vm.SDIV, v...) }
func (a *asm) Mod(v ...interface{}) *asm        { return a.opWithPush(vm.MOD, v...) }
func (a *asm) SMod(v ...interface{}) *asm       { return a.opWithPush(vm.SMOD, v...) }
func (a *asm) AddMod(v ...interface{}) *asm     { return a.opWithPush(vm.ADDMOD, v...) }
func (a *asm) MulMod(v ...interface{}) *asm     { return a.opWithPush(vm.MULMOD, v...) }
func (a *asm) Exp(v ...interface{}) *asm        { return a.opWithPush(vm.EXP, v...) }
func (a *asm) SignExtend(v ...interface{}) *asm { return a.opWithPush(vm.SIGNEXTEND, v...) }

// 0x10 range
func (a *asm) Lt(v ...interface{}) *asm     { return a.opWithPush(vm.LT, v...) }
func (a *asm) Gt(v ...interface{}) *asm     { return a.opWithPush(vm.GT, v...) }
func (a *asm) SLt(v ...interface{}) *asm    { return a.opWithPush(vm.SLT, v...) }
func (a *asm) SGt(v ...interface{}) *asm    { return a.opWithPush(vm.SGT, v...) }
func (a *asm) Eq(v ...interface{}) *asm     { return a.opWithPush(vm.EQ, v...) }
func (a *asm) IsZero(v ...interface{}) *asm { return a.opWithPush(vm.ISZERO, v...) }
func (a *asm) And(v ...interface{}) *asm    { return a.opWithPush(vm.AND, v...) }
func (a *asm) Or(v ...interface{}) *asm     { return a.opWithPush(vm.OR, v...) }
func (a *asm) Xor(v ...interface{}) *asm    { return a.opWithPush(vm.XOR, v...) }
func (a *asm) Not(v ...interface{}) *asm    { return a.opWithPush(vm.NOT, v...) }
func (a *asm) Byte(v ...interface{}) *asm   { return a.opWithPush(vm.BYTE, v...) }
func (a *asm) Shl(v ...interface{}) *asm    { return a.opWithPush(vm.SHL, v...) }
func (a *asm) Shr(v ...interface{}) *asm    { return a.opWithPush(vm.SHR, v...) }
func (a *asm) Sar(v ...interface{}) *asm    { return a.opWithPush(vm.SAR, v...) }
func (a *asm) Sha3(v ...interface{}) *asm   { return a.opWithPush(vm.SHA3, v...) }

// 0x30 range
func (a *asm) Address() *asm                        { return a.appendByte(vm.ADDRESS) }
func (a *asm) Balance(v ...interface{}) *asm        { return a.opWithPush(vm.BALANCE, v...) }
func (a *asm) Origin() *asm                         { return a.appendByte(vm.ORIGIN) }
func (a *asm) Caller() *asm                         { return a.appendByte(vm.CALLER) }
func (a *asm) CallValue() *asm                      { return a.appendByte(vm.CALLVALUE) }
func (a *asm) CallDataLoad(v ...interface{}) *asm   { return a.opWithPush(vm.CALLDATALOAD, v...) }
func (a *asm) CallDataSize() *asm                   { return a.appendByte(vm.CALLDATASIZE) }
func (a *asm) CallDataCopy(v ...interface{}) *asm   { return a.opWithPush(vm.CALLDATACOPY, v...) }
func (a *asm) CodeSize() *asm                       { return a.appendByte(vm.CODESIZE) }
func (a *asm) CodeCopy(v ...interface{}) *asm       { return a.opWithPush(vm.CODECOPY, v...) }
func (a *asm) GasPrice() *asm                       { return a.appendByte(vm.GASPRICE) }
func (a *asm) ExtCodeSize(v ...interface{}) *asm    { return a.opWithPush(vm.EXTCODESIZE, v...) }
func (a *asm) ExtCodeCopy(v ...interface{}) *asm    { return a.opWithPush(vm.EXTCODECOPY, v...) }
func (a *asm) ReturnDataSize() *asm                 { return a.appendByte(vm.RETURNDATASIZE) }
func (a *asm) ReturnDataCopy(v ...interface{}) *asm { return a.opWithPush(vm.RETURNDATACOPY, v...) }
func (a *asm) ExtCodeHash(v ...interface{}) *asm    { return a.opWithPush(vm.EXTCODEHASH, v...) }

// 0x40 range
func (a *asm) BlockHash(v ...interface{}) *asm { return a.opWithPush(vm.BLOCKHASH, v...) }
func (a *asm) Coinbase() *asm                  { return a.appendByte(vm.COINBASE) }
func (a *asm) Timestamp() *asm                 { return a.appendByte(vm.TIMESTAMP) }
func (a *asm) Number() *asm                    { return a.appendByte(vm.NUMBER) }
func (a *asm) Difficulty() *asm                { return a.appendByte(vm.DIFFICULTY) }
func (a *asm) GasLimit() *asm                  { return a.appendByte(vm.GASLIMIT) }
func (a *asm) ChainID() *asm                   { return a.appendByte(vm.CHAINID) }
func (a *asm) SelfBalance() *asm               { return a.appendByte(vm.SELFBALANCE) }
func (a *asm) BaseFee() *asm                   { return a.appendByte(vm.BASEFEE) }

// 0x50 range
func (a *asm) Pop() *asm                     { return a.appendByte(vm.POP) }
func (a *asm) MLoad(v ...interface{}) *asm   { return a.opWithPush(vm.MLOAD, v...) }
func (a *asm) MStore(v ...interface{}) *asm  { return a.opWithPush(vm.MSTORE, v...) }
func (a *asm) MStore8(v ...interface{}) *asm { return a.opWithPush(vm.MSTORE8, v...) }
func (a *asm) SLoad(v ...interface{}) *asm   { return a.opWithPush(vm.SLOAD, v...) }
func (a *asm) SStore(v ...interface{}) *asm  { return a.opWithPush(vm.SSTORE, v...) }
func (a *asm) Jump(label ...string) *asm     { return a.jump(vm.JUMP, label...) }
func (a *asm) JumpI(label ...string) *asm    { return a.jump(vm.JUMPI, label...) }
func (a *asm) PC() *asm                      { return a.appendByte(vm.PC) }
func (a *asm) MSize() *asm                   { return a.appendByte(vm.MSIZE) }
func (a *asm) Gas() *asm                     { return a.appendByte(vm.GAS) }
func (a *asm) JumpDest(label ...string) *asm { return a.jumpDest(label...) }

// 0x60 range
func (a *asm) PushX(val interface{}) *asm { return a.push(val) }
func (a *asm) DupX(x int) *asm {
	rangeCheck(x, 1, 16, "X")
	return a.appendByte(int(vm.DUP1) + x - 1)
}
func (a *asm) SwapX(x int) *asm {
	rangeCheck(x, 1, 16, "X")
	return a.appendByte(int(vm.SWAP1) + x - 1)
}

// 0xa0 range
func (a *asm) LogX(x int) *asm {
	rangeCheck(x, 0, 5, "X")
	return a.appendByte(int(vm.LOG0) + x)
}

// 0xf0 range
func (a *asm) Create(v ...interface{}) *asm       { return a.opWithPush(vm.CREATE, v...) }
func (a *asm) Call(v ...interface{}) *asm         { return a.opWithPush(vm.CALL, v...) }
func (a *asm) CallCode(v ...interface{}) *asm     { return a.opWithPush(vm.CALLCODE, v...) }
func (a *asm) Return(v ...interface{}) *asm       { return a.opWithPush(vm.RETURN, v...) }
func (a *asm) DelegateCall(v ...interface{}) *asm { return a.opWithPush(vm.DELEGATECALL, v...) }
func (a *asm) Create2(v ...interface{}) *asm      { return a.opWithPush(vm.CREATE2, v...) }
func (a *asm) StaticCall(v ...interface{}) *asm   { return a.opWithPush(vm.STATICCALL, v...) }
func (a *asm) Revert(v ...interface{}) *asm       { return a.opWithPush(vm.REVERT, v...) }
func (a *asm) SelfDestruct() *asm                 { return a.appendByte(vm.SELFDESTRUCT) }

func (a *asm) jump(op vm.OpCode, label ...string) *asm {
	if len(label) > 0 {
		rangeCheck(len(label), 1, 1, "len(label)")

		if pos, ok := a.labelMap[label[0]]; ok {
			a.PushX(pos)
		} else {
			a.pendingLabelsMap[label[0]] = append(a.pendingLabelsMap[label[0]], len(a.Bytecode))
			a.PushX([]byte{0, 0})
		}
	}

	return a.appendByte(op)
}

func (a *asm) jumpDest(label ...string) *asm {
	a.appendByte(vm.JUMPDEST)

	if len(label) > 0 {
		rangeCheck(len(label), 1, 1, "len(label)")

		if _, ok := a.labelMap[label[0]]; ok {
			panic("label already defined")
		}

		a.labelMap[label[0]] = len(a.Bytecode)

		pos := big.NewInt(int64(len(a.Bytecode) - 1)).Bytes()
		if len(pos) == 1 {
			pos = []byte{0, pos[0]}
		}
		for _, pendingLabel := range a.pendingLabelsMap[label[0]] {
			a.Bytecode[pendingLabel+1] = pos[0]
			a.Bytecode[pendingLabel+2] = pos[1]
		}

		delete(a.pendingLabelsMap, label[0])
	}

	return a
}

func (a *asm) opWithPush(op vm.OpCode, v ...interface{}) *asm {
	opPushRangeCheck(op, len(v))
	return a.pushRev(v...).appendByte(op)
}

func (a *asm) push(v ...interface{}) *asm {
	for _, v := range v {
		bytes := toBytes(v)

		rangeCheck(len(bytes), 1, 32, "len(bytes)")
		a.appendByte(int(vm.PUSH1) + len(bytes) - 1)

		for _, b := range bytes {
			a.appendByte(b)
		}
	}

	return a
}

func (a *asm) pushRev(v ...interface{}) *asm {
	reverse(v)
	return a.push(v...)
}

func (a *asm) appendByte(v interface{}) *asm {
	switch v := v.(type) {
	case vm.OpCode:
		a.Bytecode = append(a.Bytecode, byte(v))
	case byte:
		a.Bytecode = append(a.Bytecode, v)
	case int:
		a.Bytecode = append(a.Bytecode, byte(v))
	default:
		panic(fmt.Sprintf("unexpected appendByte type %T", v))
	}

	return a
}
