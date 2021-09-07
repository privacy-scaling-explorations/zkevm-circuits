use crate::error::Error;
use core::fmt::Debug;
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// Opcode enum. One-to-one corresponding to an `u8` value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct OpcodeId(pub u8);

// Core opcodes.
impl OpcodeId {
    /// `STOP`
    pub const STOP: OpcodeId = OpcodeId(0x00);
    /// `ADD`
    pub const ADD: OpcodeId = OpcodeId(0x01);
    /// `MUL`
    pub const MUL: OpcodeId = OpcodeId(0x02);
    /// `SUB`
    pub const SUB: OpcodeId = OpcodeId(0x03);
    /// `DIV`
    pub const DIV: OpcodeId = OpcodeId(0x04);
    /// `SDIV`
    pub const SDIV: OpcodeId = OpcodeId(0x05);
    /// `MOD`
    pub const MOD: OpcodeId = OpcodeId(0x06);
    /// `SMOD`
    pub const SMOD: OpcodeId = OpcodeId(0x07);
    /// `ADDMOD`
    pub const ADDMOD: OpcodeId = OpcodeId(0x08);
    /// `MULMOD`
    pub const MULMOD: OpcodeId = OpcodeId(0x09);
    /// `EXP`
    pub const EXP: OpcodeId = OpcodeId(0x0a);
    /// `SIGNEXTEND`
    pub const SIGNEXTEND: OpcodeId = OpcodeId(0x0b);

    /// `LT`
    pub const LT: OpcodeId = OpcodeId(0x10);
    /// `GT`
    pub const GT: OpcodeId = OpcodeId(0x11);
    /// `SLT`
    pub const SLT: OpcodeId = OpcodeId(0x12);
    /// `SGT`
    pub const SGT: OpcodeId = OpcodeId(0x13);
    /// `EQ`
    pub const EQ: OpcodeId = OpcodeId(0x14);
    /// `ISZERO`
    pub const ISZERO: OpcodeId = OpcodeId(0x15);
    /// `AND`
    pub const AND: OpcodeId = OpcodeId(0x16);
    /// `OR`
    pub const OR: OpcodeId = OpcodeId(0x17);
    /// `XOR`
    pub const XOR: OpcodeId = OpcodeId(0x18);
    /// `NOT`
    pub const NOT: OpcodeId = OpcodeId(0x19);
    /// `BYTE`
    pub const BYTE: OpcodeId = OpcodeId(0x1a);

    /// `CALLDATALOAD`
    pub const CALLDATALOAD: OpcodeId = OpcodeId(0x35);
    /// `CALLDATASIZE`
    pub const CALLDATASIZE: OpcodeId = OpcodeId(0x36);
    /// `CALLDATACOPY`
    pub const CALLDATACOPY: OpcodeId = OpcodeId(0x37);
    /// `CODESIZE`
    pub const CODESIZE: OpcodeId = OpcodeId(0x38);
    /// `CODECOPY`
    pub const CODECOPY: OpcodeId = OpcodeId(0x39);

    /// `SHL`
    pub const SHL: OpcodeId = OpcodeId(0x1b);
    /// `SHR`
    pub const SHR: OpcodeId = OpcodeId(0x1c);
    /// `SAR`
    pub const SAR: OpcodeId = OpcodeId(0x1d);

    /// `POP`
    pub const POP: OpcodeId = OpcodeId(0x50);
    /// `MLOAD`
    pub const MLOAD: OpcodeId = OpcodeId(0x51);
    /// `MSTORE`
    pub const MSTORE: OpcodeId = OpcodeId(0x52);
    /// `MSTORE8`
    pub const MSTORE8: OpcodeId = OpcodeId(0x53);
    /// `JUMP`
    pub const JUMP: OpcodeId = OpcodeId(0x56);
    /// `JUMPI`
    pub const JUMPI: OpcodeId = OpcodeId(0x57);
    /// `PC`
    pub const PC: OpcodeId = OpcodeId(0x58);
    /// `MSIZE`
    pub const MSIZE: OpcodeId = OpcodeId(0x59);
    /// `JUMPDEST`
    pub const JUMPDEST: OpcodeId = OpcodeId(0x5b);

    // PUSHn
    /// `PUSH1`
    pub const PUSH1: OpcodeId = OpcodeId(0x60);
    /// `PUSH2`
    pub const PUSH2: OpcodeId = OpcodeId(0x61);
    /// `PUSH3`
    pub const PUSH3: OpcodeId = OpcodeId(0x62);
    /// `PUSH4`
    pub const PUSH4: OpcodeId = OpcodeId(0x63);
    /// `PUSH5`
    pub const PUSH5: OpcodeId = OpcodeId(0x64);
    /// `PUSH6`
    pub const PUSH6: OpcodeId = OpcodeId(0x65);
    /// `PUSH7`
    pub const PUSH7: OpcodeId = OpcodeId(0x66);
    /// `PUSH8`
    pub const PUSH8: OpcodeId = OpcodeId(0x67);
    /// `PUSH9`
    pub const PUSH9: OpcodeId = OpcodeId(0x68);
    /// `PUSH10`
    pub const PUSH10: OpcodeId = OpcodeId(0x69);
    /// `PUSH11`
    pub const PUSH11: OpcodeId = OpcodeId(0x6a);
    /// `PUSH12`
    pub const PUSH12: OpcodeId = OpcodeId(0x6b);
    /// `PUSH13`
    pub const PUSH13: OpcodeId = OpcodeId(0x6c);
    /// `PUSH14`
    pub const PUSH14: OpcodeId = OpcodeId(0x6d);
    /// `PUSH15`
    pub const PUSH15: OpcodeId = OpcodeId(0x6e);
    /// `PUSH16`
    pub const PUSH16: OpcodeId = OpcodeId(0x6f);
    /// `PUSH17`
    pub const PUSH17: OpcodeId = OpcodeId(0x70);
    /// `PUSH18`
    pub const PUSH18: OpcodeId = OpcodeId(0x71);
    /// `PUSH19`
    pub const PUSH19: OpcodeId = OpcodeId(0x72);
    /// `PUSH20`
    pub const PUSH20: OpcodeId = OpcodeId(0x73);
    /// `PUSH21`
    pub const PUSH21: OpcodeId = OpcodeId(0x74);
    /// `PUSH22`
    pub const PUSH22: OpcodeId = OpcodeId(0x75);
    /// `PUSH23`
    pub const PUSH23: OpcodeId = OpcodeId(0x76);
    /// `PUSH24`
    pub const PUSH24: OpcodeId = OpcodeId(0x77);
    /// `PUSH25`
    pub const PUSH25: OpcodeId = OpcodeId(0x78);
    /// `PUSH26`
    pub const PUSH26: OpcodeId = OpcodeId(0x79);
    /// `PUSH27`
    pub const PUSH27: OpcodeId = OpcodeId(0x7a);
    /// `PUSH28`
    pub const PUSH28: OpcodeId = OpcodeId(0x7b);
    /// `PUSH29`
    pub const PUSH29: OpcodeId = OpcodeId(0x7c);
    /// `PUSH30`
    pub const PUSH30: OpcodeId = OpcodeId(0x7d);
    /// `PUSH31`
    pub const PUSH31: OpcodeId = OpcodeId(0x7e);
    /// `PUSH32`
    pub const PUSH32: OpcodeId = OpcodeId(0x7f);

    // DUPn
    /// `DUP1`
    pub const DUP1: OpcodeId = OpcodeId(0x80);
    /// `DUP2`
    pub const DUP2: OpcodeId = OpcodeId(0x81);
    /// `DUP3`
    pub const DUP3: OpcodeId = OpcodeId(0x82);
    /// `DUP4`
    pub const DUP4: OpcodeId = OpcodeId(0x83);
    /// `DUP5`
    pub const DUP5: OpcodeId = OpcodeId(0x84);
    /// `DUP6`
    pub const DUP6: OpcodeId = OpcodeId(0x85);
    /// `DUP7`
    pub const DUP7: OpcodeId = OpcodeId(0x86);
    /// `DUP8`
    pub const DUP8: OpcodeId = OpcodeId(0x87);
    /// `DUP9`
    pub const DUP9: OpcodeId = OpcodeId(0x88);
    /// `DUP10`
    pub const DUP10: OpcodeId = OpcodeId(0x89);
    /// `DUP11`
    pub const DUP11: OpcodeId = OpcodeId(0x8a);
    /// `DUP12`
    pub const DUP12: OpcodeId = OpcodeId(0x8b);
    /// `DUP13`
    pub const DUP13: OpcodeId = OpcodeId(0x8c);
    /// `DUP14`
    pub const DUP14: OpcodeId = OpcodeId(0x8d);
    /// `DUP15`
    pub const DUP15: OpcodeId = OpcodeId(0x8e);
    /// `DUP16`
    pub const DUP16: OpcodeId = OpcodeId(0x8f);

    // SWAPn
    /// `SWAP1`
    pub const SWAP1: OpcodeId = OpcodeId(0x90);
    /// `SWAP2`
    pub const SWAP2: OpcodeId = OpcodeId(0x91);
    /// `SWAP3`
    pub const SWAP3: OpcodeId = OpcodeId(0x92);
    /// `SWAP4`
    pub const SWAP4: OpcodeId = OpcodeId(0x93);
    /// `SWAP5`
    pub const SWAP5: OpcodeId = OpcodeId(0x94);
    /// `SWAP6`
    pub const SWAP6: OpcodeId = OpcodeId(0x95);
    /// `SWAP7`
    pub const SWAP7: OpcodeId = OpcodeId(0x96);
    /// `SWAP8`
    pub const SWAP8: OpcodeId = OpcodeId(0x97);
    /// `SWAP9`
    pub const SWAP9: OpcodeId = OpcodeId(0x98);
    /// `SWAP10`
    pub const SWAP10: OpcodeId = OpcodeId(0x99);
    /// `SWAP11`
    pub const SWAP11: OpcodeId = OpcodeId(0x9a);
    /// `SWAP12`
    pub const SWAP12: OpcodeId = OpcodeId(0x9b);
    /// `SWAP13`
    pub const SWAP13: OpcodeId = OpcodeId(0x9c);
    /// `SWAP14`
    pub const SWAP14: OpcodeId = OpcodeId(0x9d);
    /// `SWAP15`
    pub const SWAP15: OpcodeId = OpcodeId(0x9e);
    /// `SWAP16`
    pub const SWAP16: OpcodeId = OpcodeId(0x9f);

    /// `RETURN`
    pub const RETURN: OpcodeId = OpcodeId(0xf3);
    /// `REVERT`
    pub const REVERT: OpcodeId = OpcodeId(0xfd);

    /// `INVALID`
    pub const INVALID: OpcodeId = OpcodeId(0xfe);
}

// External opcodes
impl OpcodeId {
    /// `SHA3`
    pub const SHA3: OpcodeId = OpcodeId(0x20);
    /// `ADDRESS`
    pub const ADDRESS: OpcodeId = OpcodeId(0x30);
    /// `BALANCE`
    pub const BALANCE: OpcodeId = OpcodeId(0x31);
    /// `ORIGIN`
    pub const ORIGIN: OpcodeId = OpcodeId(0x32);
    /// `CALLER`
    pub const CALLER: OpcodeId = OpcodeId(0x33);
    /// `CALLVALUE`
    pub const CALLVALUE: OpcodeId = OpcodeId(0x34);
    /// `GASPRICE`
    pub const GASPRICE: OpcodeId = OpcodeId(0x3a);
    /// `EXTCODESIZE`
    pub const EXTCODESIZE: OpcodeId = OpcodeId(0x3b);
    /// `EXTCODECOPY`
    pub const EXTCODECOPY: OpcodeId = OpcodeId(0x3c);
    /// `EXTCODEHASH`
    pub const EXTCODEHASH: OpcodeId = OpcodeId(0x3f);
    /// `RETURNDATASIZE`
    pub const RETURNDATASIZE: OpcodeId = OpcodeId(0x3d);
    /// `RETURNDATACOPY`
    pub const RETURNDATACOPY: OpcodeId = OpcodeId(0x3e);
    /// `BLOCKHASH`
    pub const BLOCKHASH: OpcodeId = OpcodeId(0x40);
    /// `COINBASE`
    pub const COINBASE: OpcodeId = OpcodeId(0x41);
    /// `TIMESTAMP`
    pub const TIMESTAMP: OpcodeId = OpcodeId(0x42);
    /// `NUMBER`
    pub const NUMBER: OpcodeId = OpcodeId(0x43);
    /// `DIFFICULTY`
    pub const DIFFICULTY: OpcodeId = OpcodeId(0x44);
    /// `GASLIMIT`
    pub const GASLIMIT: OpcodeId = OpcodeId(0x45);
    /// `CHAINID`
    pub const CHAINID: OpcodeId = OpcodeId(0x46);
    /// `SELFBALANCE`
    pub const SELFBALANCE: OpcodeId = OpcodeId(0x47);
    /// `BASEFEE`
    pub const BASEFEE: OpcodeId = OpcodeId(0x48);
    /// `SLOAD`
    pub const SLOAD: OpcodeId = OpcodeId(0x54);
    /// `SSTORE`
    pub const SSTORE: OpcodeId = OpcodeId(0x55);
    /// `GAS`
    pub const GAS: OpcodeId = OpcodeId(0x5a);

    // LOGn
    /// `LOG0`
    pub const LOG0: OpcodeId = OpcodeId(0xa0);
    /// `LOG1`
    pub const LOG1: OpcodeId = OpcodeId(0xa1);
    /// `LOG2`
    pub const LOG2: OpcodeId = OpcodeId(0xa2);
    /// `LOG3`
    pub const LOG3: OpcodeId = OpcodeId(0xa3);
    /// `LOG4`
    pub const LOG4: OpcodeId = OpcodeId(0xa4);

    /// `CREATE`
    pub const CREATE: OpcodeId = OpcodeId(0xf0);
    /// `CREATE2`
    pub const CREATE2: OpcodeId = OpcodeId(0xf5);
    /// `CALL`
    pub const CALL: OpcodeId = OpcodeId(0xf1);
    /// `CALLCODE`
    pub const CALLCODE: OpcodeId = OpcodeId(0xf2);
    /// `DELEGATECALL`
    pub const DELEGATECALL: OpcodeId = OpcodeId(0xf4);
    /// `STATICCALL`
    pub const STATICCALL: OpcodeId = OpcodeId(0xfa);
    /// `SELFDESTRUCT`
    pub const SELFDESTRUCT: OpcodeId = OpcodeId(0xff);
}

impl OpcodeId {
    /// Returns the `OpcodeId` as a `u8`.
    #[inline]
    pub const fn as_u8(&self) -> u8 {
        self.0
    }

    /// Returns the `OpcodeId` as a `usize`.
    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl FromStr for OpcodeId {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "STOP" => OpcodeId::STOP,
            "ADD" => OpcodeId::ADD,
            "MUL" => OpcodeId::MUL,
            "SUB" => OpcodeId::SUB,
            "DIV" => OpcodeId::DIV,
            "SDIV" => OpcodeId::SDIV,
            "MOD" => OpcodeId::MOD,
            "SMOD" => OpcodeId::SMOD,
            "ADDMOD" => OpcodeId::ADDMOD,
            "MULMOD" => OpcodeId::MULMOD,
            "EXP" => OpcodeId::EXP,
            "SIGNEXTEND" => OpcodeId::SIGNEXTEND,
            "LT" => OpcodeId::LT,
            "GT" => OpcodeId::GT,
            "SLT" => OpcodeId::SLT,
            "SGT" => OpcodeId::SGT,
            "EQ" => OpcodeId::EQ,
            "ISZERO" => OpcodeId::ISZERO,
            "AND" => OpcodeId::AND,
            "OR" => OpcodeId::OR,
            "XOR" => OpcodeId::XOR,
            "NOT" => OpcodeId::NOT,
            "BYTE" => OpcodeId::BYTE,
            "CALLDATALOAD" => OpcodeId::CALLDATALOAD,
            "CALLDATASIZE" => OpcodeId::CALLDATASIZE,
            "CALLDATACOPY" => OpcodeId::CALLDATACOPY,
            "CODESIZE" => OpcodeId::CODESIZE,
            "CODECOPY" => OpcodeId::CODECOPY,
            "SHL" => OpcodeId::SHL,
            "SHR" => OpcodeId::SHR,
            "SAR" => OpcodeId::SAR,
            "POP" => OpcodeId::POP,
            "MLOAD" => OpcodeId::MLOAD,
            "MSTORE" => OpcodeId::MSTORE,
            "MSTORE8" => OpcodeId::MSTORE8,
            "JUMP" => OpcodeId::JUMP,
            "JUMPI" => OpcodeId::JUMPI,
            "PC" => OpcodeId::PC,
            "MSIZE" => OpcodeId::MSIZE,
            "JUMPDEST" => OpcodeId::JUMPDEST,
            "PUSH1" => OpcodeId::PUSH1,
            "PUSH2" => OpcodeId::PUSH2,
            "PUSH3" => OpcodeId::PUSH3,
            "PUSH4" => OpcodeId::PUSH4,
            "PUSH5" => OpcodeId::PUSH5,
            "PUSH6" => OpcodeId::PUSH6,
            "PUSH7" => OpcodeId::PUSH7,
            "PUSH8" => OpcodeId::PUSH8,
            "PUSH9" => OpcodeId::PUSH9,
            "PUSH10" => OpcodeId::PUSH10,
            "PUSH11" => OpcodeId::PUSH11,
            "PUSH12" => OpcodeId::PUSH12,
            "PUSH13" => OpcodeId::PUSH13,
            "PUSH14" => OpcodeId::PUSH14,
            "PUSH15" => OpcodeId::PUSH15,
            "PUSH16" => OpcodeId::PUSH16,
            "PUSH17" => OpcodeId::PUSH17,
            "PUSH18" => OpcodeId::PUSH18,
            "PUSH19" => OpcodeId::PUSH19,
            "PUSH20" => OpcodeId::PUSH20,
            "PUSH21" => OpcodeId::PUSH21,
            "PUSH22" => OpcodeId::PUSH22,
            "PUSH23" => OpcodeId::PUSH23,
            "PUSH24" => OpcodeId::PUSH24,
            "PUSH25" => OpcodeId::PUSH25,
            "PUSH26" => OpcodeId::PUSH26,
            "PUSH27" => OpcodeId::PUSH27,
            "PUSH28" => OpcodeId::PUSH28,
            "PUSH29" => OpcodeId::PUSH29,
            "PUSH30" => OpcodeId::PUSH30,
            "PUSH31" => OpcodeId::PUSH31,
            "PUSH32" => OpcodeId::PUSH32,
            "DUP1" => OpcodeId::DUP1,
            "DUP2" => OpcodeId::DUP2,
            "DUP3" => OpcodeId::DUP3,
            "DUP4" => OpcodeId::DUP4,
            "DUP5" => OpcodeId::DUP5,
            "DUP6" => OpcodeId::DUP6,
            "DUP7" => OpcodeId::DUP7,
            "DUP8" => OpcodeId::DUP8,
            "DUP9" => OpcodeId::DUP9,
            "DUP10" => OpcodeId::DUP10,
            "DUP11" => OpcodeId::DUP11,
            "DUP12" => OpcodeId::DUP12,
            "DUP13" => OpcodeId::DUP13,
            "DUP14" => OpcodeId::DUP14,
            "DUP15" => OpcodeId::DUP15,
            "DUP16" => OpcodeId::DUP16,
            "SWAP1" => OpcodeId::SWAP1,
            "SWAP2" => OpcodeId::SWAP2,
            "SWAP3" => OpcodeId::SWAP3,
            "SWAP4" => OpcodeId::SWAP4,
            "SWAP5" => OpcodeId::SWAP5,
            "SWAP6" => OpcodeId::SWAP6,
            "SWAP7" => OpcodeId::SWAP7,
            "SWAP8" => OpcodeId::SWAP8,
            "SWAP9" => OpcodeId::SWAP9,
            "SWAP10" => OpcodeId::SWAP10,
            "SWAP11" => OpcodeId::SWAP11,
            "SWAP12" => OpcodeId::SWAP12,
            "SWAP13" => OpcodeId::SWAP13,
            "SWAP14" => OpcodeId::SWAP14,
            "SWAP15" => OpcodeId::SWAP15,
            "SWAP16" => OpcodeId::SWAP16,
            "RETURN" => OpcodeId::RETURN,
            "REVERT" => OpcodeId::REVERT,
            "INVALID" => OpcodeId::INVALID,
            "SHA3" => OpcodeId::SHA3,
            "ADDRESS" => OpcodeId::ADDRESS,
            "BALANCE" => OpcodeId::BALANCE,
            "SELFBALANCE" => OpcodeId::SELFBALANCE,
            "ORIGIN" => OpcodeId::ORIGIN,
            "CALLER" => OpcodeId::CALLER,
            "CALLVALUE" => OpcodeId::CALLVALUE,
            "GASPRICE" => OpcodeId::GASPRICE,
            "EXTCODESIZE" => OpcodeId::EXTCODESIZE,
            "EXTCODECOPY" => OpcodeId::EXTCODECOPY,
            "EXTCODEHASH" => OpcodeId::EXTCODEHASH,
            "RETURNDATASIZE" => OpcodeId::RETURNDATASIZE,
            "RETURNDATACOPY" => OpcodeId::RETURNDATACOPY,
            "BLOCKHASH" => OpcodeId::BLOCKHASH,
            "COINBASE" => OpcodeId::COINBASE,
            "TIMESTAMP" => OpcodeId::TIMESTAMP,
            "NUMBER" => OpcodeId::NUMBER,
            "DIFFICULTY" => OpcodeId::DIFFICULTY,
            "GASLIMIT" => OpcodeId::GASLIMIT,
            "SLOAD" => OpcodeId::SLOAD,
            "SSTORE" => OpcodeId::SSTORE,
            "GAS" => OpcodeId::GAS,
            "LOG0" => OpcodeId::LOG0,
            "LOG1" => OpcodeId::LOG1,
            "LOG2" => OpcodeId::LOG2,
            "LOG3" => OpcodeId::LOG3,
            "LOG4" => OpcodeId::LOG4,
            "CREATE" => OpcodeId::CREATE,
            "CREATE2" => OpcodeId::CREATE2,
            "CALL" => OpcodeId::CALL,
            "CALLCODE" => OpcodeId::CALLCODE,
            "DELEGATECALL" => OpcodeId::DELEGATECALL,
            "STATICCALL" => OpcodeId::STATICCALL,
            "SELFDESTRUCT" => OpcodeId::SELFDESTRUCT,
            "CHAINID" => OpcodeId::CHAINID,
            "BASEFEE" => OpcodeId::BASEFEE,
            _ => return Err(Error::OpcodeParsing),
        })
    }
}
