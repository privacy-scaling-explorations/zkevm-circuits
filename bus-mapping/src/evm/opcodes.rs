//! Definition of each opcode of the EVM.

use serde::{Deserialize, Serialize};
use std::str::FromStr;

use crate::error::Error;

/// Opcode enum. One-to-one corresponding to an `u8` value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Opcode(pub u8);

// Core opcodes.
impl Opcode {
    /// `STOP`
    pub const STOP: Opcode = Opcode(0x00);
    /// `ADD`
    pub const ADD: Opcode = Opcode(0x01);
    /// `MUL`
    pub const MUL: Opcode = Opcode(0x02);
    /// `SUB`
    pub const SUB: Opcode = Opcode(0x03);
    /// `DIV`
    pub const DIV: Opcode = Opcode(0x04);
    /// `SDIV`
    pub const SDIV: Opcode = Opcode(0x05);
    /// `MOD`
    pub const MOD: Opcode = Opcode(0x06);
    /// `SMOD`
    pub const SMOD: Opcode = Opcode(0x07);
    /// `ADDMOD`
    pub const ADDMOD: Opcode = Opcode(0x08);
    /// `MULMOD`
    pub const MULMOD: Opcode = Opcode(0x09);
    /// `EXP`
    pub const EXP: Opcode = Opcode(0x0a);
    /// `SIGNEXTEND`
    pub const SIGNEXTEND: Opcode = Opcode(0x0b);

    /// `LT`
    pub const LT: Opcode = Opcode(0x10);
    /// `GT`
    pub const GT: Opcode = Opcode(0x11);
    /// `SLT`
    pub const SLT: Opcode = Opcode(0x12);
    /// `SGT`
    pub const SGT: Opcode = Opcode(0x13);
    /// `EQ`
    pub const EQ: Opcode = Opcode(0x14);
    /// `ISZERO`
    pub const ISZERO: Opcode = Opcode(0x15);
    /// `AND`
    pub const AND: Opcode = Opcode(0x16);
    /// `OR`
    pub const OR: Opcode = Opcode(0x17);
    /// `XOR`
    pub const XOR: Opcode = Opcode(0x18);
    /// `NOT`
    pub const NOT: Opcode = Opcode(0x19);
    /// `BYTE`
    pub const BYTE: Opcode = Opcode(0x1a);

    /// `CALLDATALOAD`
    pub const CALLDATALOAD: Opcode = Opcode(0x35);
    /// `CALLDATASIZE`
    pub const CALLDATASIZE: Opcode = Opcode(0x36);
    /// `CALLDATACOPY`
    pub const CALLDATACOPY: Opcode = Opcode(0x37);
    /// `CODESIZE`
    pub const CODESIZE: Opcode = Opcode(0x38);
    /// `CODECOPY`
    pub const CODECOPY: Opcode = Opcode(0x39);

    /// `SHL`
    pub const SHL: Opcode = Opcode(0x1b);
    /// `SHR`
    pub const SHR: Opcode = Opcode(0x1c);
    /// `SAR`
    pub const SAR: Opcode = Opcode(0x1d);

    /// `POP`
    pub const POP: Opcode = Opcode(0x50);
    /// `MLOAD`
    pub const MLOAD: Opcode = Opcode(0x51);
    /// `MSTORE`
    pub const MSTORE: Opcode = Opcode(0x52);
    /// `MSTORE8`
    pub const MSTORE8: Opcode = Opcode(0x53);
    /// `JUMP`
    pub const JUMP: Opcode = Opcode(0x56);
    /// `JUMPI`
    pub const JUMPI: Opcode = Opcode(0x57);
    /// `PC`
    pub const PC: Opcode = Opcode(0x58);
    /// `MSIZE`
    pub const MSIZE: Opcode = Opcode(0x59);
    /// `JUMPDEST`
    pub const JUMPDEST: Opcode = Opcode(0x5b);

    /// `PUSHn`
    pub const PUSH1: Opcode = Opcode(0x60);
    pub const PUSH2: Opcode = Opcode(0x61);
    pub const PUSH3: Opcode = Opcode(0x62);
    pub const PUSH4: Opcode = Opcode(0x63);
    pub const PUSH5: Opcode = Opcode(0x64);
    pub const PUSH6: Opcode = Opcode(0x65);
    pub const PUSH7: Opcode = Opcode(0x66);
    pub const PUSH8: Opcode = Opcode(0x67);
    pub const PUSH9: Opcode = Opcode(0x68);
    pub const PUSH10: Opcode = Opcode(0x69);
    pub const PUSH11: Opcode = Opcode(0x6a);
    pub const PUSH12: Opcode = Opcode(0x6b);
    pub const PUSH13: Opcode = Opcode(0x6c);
    pub const PUSH14: Opcode = Opcode(0x6d);
    pub const PUSH15: Opcode = Opcode(0x6e);
    pub const PUSH16: Opcode = Opcode(0x6f);
    pub const PUSH17: Opcode = Opcode(0x70);
    pub const PUSH18: Opcode = Opcode(0x71);
    pub const PUSH19: Opcode = Opcode(0x72);
    pub const PUSH20: Opcode = Opcode(0x73);
    pub const PUSH21: Opcode = Opcode(0x74);
    pub const PUSH22: Opcode = Opcode(0x75);
    pub const PUSH23: Opcode = Opcode(0x76);
    pub const PUSH24: Opcode = Opcode(0x77);
    pub const PUSH25: Opcode = Opcode(0x78);
    pub const PUSH26: Opcode = Opcode(0x79);
    pub const PUSH27: Opcode = Opcode(0x7a);
    pub const PUSH28: Opcode = Opcode(0x7b);
    pub const PUSH29: Opcode = Opcode(0x7c);
    pub const PUSH30: Opcode = Opcode(0x7d);
    pub const PUSH31: Opcode = Opcode(0x7e);
    pub const PUSH32: Opcode = Opcode(0x7f);

    /// `DUPn`
    pub const DUP1: Opcode = Opcode(0x80);
    pub const DUP2: Opcode = Opcode(0x81);
    pub const DUP3: Opcode = Opcode(0x82);
    pub const DUP4: Opcode = Opcode(0x83);
    pub const DUP5: Opcode = Opcode(0x84);
    pub const DUP6: Opcode = Opcode(0x85);
    pub const DUP7: Opcode = Opcode(0x86);
    pub const DUP8: Opcode = Opcode(0x87);
    pub const DUP9: Opcode = Opcode(0x88);
    pub const DUP10: Opcode = Opcode(0x89);
    pub const DUP11: Opcode = Opcode(0x8a);
    pub const DUP12: Opcode = Opcode(0x8b);
    pub const DUP13: Opcode = Opcode(0x8c);
    pub const DUP14: Opcode = Opcode(0x8d);
    pub const DUP15: Opcode = Opcode(0x8e);
    pub const DUP16: Opcode = Opcode(0x8f);

    /// `SWAPn`
    pub const SWAP1: Opcode = Opcode(0x90);
    pub const SWAP2: Opcode = Opcode(0x91);
    pub const SWAP3: Opcode = Opcode(0x92);
    pub const SWAP4: Opcode = Opcode(0x93);
    pub const SWAP5: Opcode = Opcode(0x94);
    pub const SWAP6: Opcode = Opcode(0x95);
    pub const SWAP7: Opcode = Opcode(0x96);
    pub const SWAP8: Opcode = Opcode(0x97);
    pub const SWAP9: Opcode = Opcode(0x98);
    pub const SWAP10: Opcode = Opcode(0x99);
    pub const SWAP11: Opcode = Opcode(0x9a);
    pub const SWAP12: Opcode = Opcode(0x9b);
    pub const SWAP13: Opcode = Opcode(0x9c);
    pub const SWAP14: Opcode = Opcode(0x9d);
    pub const SWAP15: Opcode = Opcode(0x9e);
    pub const SWAP16: Opcode = Opcode(0x9f);

    /// `RETURN`
    pub const RETURN: Opcode = Opcode(0xf3);
    /// `REVERT`
    pub const REVERT: Opcode = Opcode(0xfd);

    /// `INVALID`
    pub const INVALID: Opcode = Opcode(0xfe);
}

// External opcodes
impl Opcode {
    /// `SHA3`
    pub const SHA3: Opcode = Opcode(0x20);
    /// `ADDRESS`
    pub const ADDRESS: Opcode = Opcode(0x30);
    /// `BALANCE`
    pub const BALANCE: Opcode = Opcode(0x31);
    /// `SELFBALANCE`
    pub const SELFBALANCE: Opcode = Opcode(0x47);
    /// `ORIGIN`
    pub const ORIGIN: Opcode = Opcode(0x32);
    /// `CALLER`
    pub const CALLER: Opcode = Opcode(0x33);
    /// `CALLVALUE`
    pub const CALLVALUE: Opcode = Opcode(0x34);
    /// `GASPRICE`
    pub const GASPRICE: Opcode = Opcode(0x3a);
    /// `EXTCODESIZE`
    pub const EXTCODESIZE: Opcode = Opcode(0x3b);
    /// `EXTCODECOPY`
    pub const EXTCODECOPY: Opcode = Opcode(0x3c);
    /// `EXTCODEHASH`
    pub const EXTCODEHASH: Opcode = Opcode(0x3f);
    /// `RETURNDATASIZE`
    pub const RETURNDATASIZE: Opcode = Opcode(0x3d);
    /// `RETURNDATACOPY`
    pub const RETURNDATACOPY: Opcode = Opcode(0x3e);
    /// `BLOCKHASH`
    pub const BLOCKHASH: Opcode = Opcode(0x40);
    /// `COINBASE`
    pub const COINBASE: Opcode = Opcode(0x41);
    /// `TIMESTAMP`
    pub const TIMESTAMP: Opcode = Opcode(0x42);
    /// `NUMBER`
    pub const NUMBER: Opcode = Opcode(0x43);
    /// `DIFFICULTY`
    pub const DIFFICULTY: Opcode = Opcode(0x44);
    /// `GASLIMIT`
    pub const GASLIMIT: Opcode = Opcode(0x45);
    /// `SLOAD`
    pub const SLOAD: Opcode = Opcode(0x54);
    /// `SSTORE`
    pub const SSTORE: Opcode = Opcode(0x55);
    /// `GAS`
    pub const GAS: Opcode = Opcode(0x5a);
    /// `LOGn`
    pub const LOG0: Opcode = Opcode(0xa0);
    pub const LOG1: Opcode = Opcode(0xa1);
    pub const LOG2: Opcode = Opcode(0xa2);
    pub const LOG3: Opcode = Opcode(0xa3);
    pub const LOG4: Opcode = Opcode(0xa4);
    /// `CREATE`
    pub const CREATE: Opcode = Opcode(0xf0);
    /// `CREATE2`
    pub const CREATE2: Opcode = Opcode(0xf5);
    /// `CALL`
    pub const CALL: Opcode = Opcode(0xf1);
    /// `CALLCODE`
    pub const CALLCODE: Opcode = Opcode(0xf2);
    /// `DELEGATECALL`
    pub const DELEGATECALL: Opcode = Opcode(0xf4);
    /// `STATICCALL`
    pub const STATICCALL: Opcode = Opcode(0xfa);
    /// `SUICIDE`
    pub const SUICIDE: Opcode = Opcode(0xff);
    /// `CHAINID`
    pub const CHAINID: Opcode = Opcode(0x46);
}

impl Opcode {
    #[inline]
    pub const fn as_u8(&self) -> u8 {
        self.0
    }

    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl FromStr for Opcode {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "STOP" => Opcode::STOP,
            "ADD" => Opcode::ADD,
            "MUL" => Opcode::MUL,
            "SUB" => Opcode::SUB,
            "DIV" => Opcode::DIV,
            "SDIV" => Opcode::SDIV,
            "MOD" => Opcode::MOD,
            "SMOD" => Opcode::SMOD,
            "ADDMOD" => Opcode::ADDMOD,
            "MULMOD" => Opcode::MULMOD,
            "EXP" => Opcode::EXP,
            "SIGNEXTEND" => Opcode::SIGNEXTEND,
            "LT" => Opcode::LT,
            "GT" => Opcode::GT,
            "SLT" => Opcode::SLT,
            "SGT" => Opcode::SGT,
            "EQ" => Opcode::EQ,
            "ISZERO" => Opcode::ISZERO,
            "AND" => Opcode::AND,
            "OR" => Opcode::OR,
            "XOR" => Opcode::XOR,
            "NOT" => Opcode::NOT,
            "BYTE" => Opcode::BYTE,
            "CALLDATALOAD" => Opcode::CALLDATALOAD,
            "CALLDATASIZE" => Opcode::CALLDATASIZE,
            "CALLDATACOPY" => Opcode::CALLDATACOPY,
            "CODESIZE" => Opcode::CODESIZE,
            "CODECOPY" => Opcode::CODECOPY,
            "SHL" => Opcode::SHL,
            "SHR" => Opcode::SHR,
            "SAR" => Opcode::SAR,
            "POP" => Opcode::POP,
            "MLOAD" => Opcode::MLOAD,
            "MSTORE" => Opcode::MSTORE,
            "MSTORE8" => Opcode::MSTORE8,
            "JUMP" => Opcode::JUMP,
            "JUMPI" => Opcode::JUMPI,
            "PC" => Opcode::PC,
            "MSIZE" => Opcode::MSIZE,
            "JUMPDEST" => Opcode::JUMPDEST,
            "PUSH1" => Opcode::PUSH1,
            "PUSH2" => Opcode::PUSH2,
            "PUSH3" => Opcode::PUSH3,
            "PUSH4" => Opcode::PUSH4,
            "PUSH5" => Opcode::PUSH5,
            "PUSH6" => Opcode::PUSH6,
            "PUSH7" => Opcode::PUSH7,
            "PUSH8" => Opcode::PUSH8,
            "PUSH9" => Opcode::PUSH9,
            "PUSH10" => Opcode::PUSH10,
            "PUSH11" => Opcode::PUSH11,
            "PUSH12" => Opcode::PUSH12,
            "PUSH13" => Opcode::PUSH13,
            "PUSH14" => Opcode::PUSH14,
            "PUSH15" => Opcode::PUSH15,
            "PUSH16" => Opcode::PUSH16,
            "PUSH17" => Opcode::PUSH17,
            "PUSH18" => Opcode::PUSH18,
            "PUSH19" => Opcode::PUSH19,
            "PUSH20" => Opcode::PUSH20,
            "PUSH21" => Opcode::PUSH21,
            "PUSH22" => Opcode::PUSH22,
            "PUSH23" => Opcode::PUSH23,
            "PUSH24" => Opcode::PUSH24,
            "PUSH25" => Opcode::PUSH25,
            "PUSH26" => Opcode::PUSH26,
            "PUSH27" => Opcode::PUSH27,
            "PUSH28" => Opcode::PUSH28,
            "PUSH29" => Opcode::PUSH29,
            "PUSH30" => Opcode::PUSH30,
            "PUSH31" => Opcode::PUSH31,
            "PUSH32" => Opcode::PUSH32,
            "DUP1" => Opcode::DUP1,
            "DUP2" => Opcode::DUP2,
            "DUP3" => Opcode::DUP3,
            "DUP4" => Opcode::DUP4,
            "DUP5" => Opcode::DUP5,
            "DUP6" => Opcode::DUP6,
            "DUP7" => Opcode::DUP7,
            "DUP8" => Opcode::DUP8,
            "DUP9" => Opcode::DUP9,
            "DUP10" => Opcode::DUP10,
            "DUP11" => Opcode::DUP11,
            "DUP12" => Opcode::DUP12,
            "DUP13" => Opcode::DUP13,
            "DUP14" => Opcode::DUP14,
            "DUP15" => Opcode::DUP15,
            "DUP16" => Opcode::DUP16,
            "SWAP1" => Opcode::SWAP1,
            "SWAP2" => Opcode::SWAP2,
            "SWAP3" => Opcode::SWAP3,
            "SWAP4" => Opcode::SWAP4,
            "SWAP5" => Opcode::SWAP5,
            "SWAP6" => Opcode::SWAP6,
            "SWAP7" => Opcode::SWAP7,
            "SWAP8" => Opcode::SWAP8,
            "SWAP9" => Opcode::SWAP9,
            "SWAP10" => Opcode::SWAP10,
            "SWAP11" => Opcode::SWAP11,
            "SWAP12" => Opcode::SWAP12,
            "SWAP13" => Opcode::SWAP13,
            "SWAP14" => Opcode::SWAP14,
            "SWAP15" => Opcode::SWAP15,
            "SWAP16" => Opcode::SWAP16,
            "RETURN" => Opcode::RETURN,
            "REVERT" => Opcode::REVERT,
            "INVALID" => Opcode::INVALID,
            "SHA3" => Opcode::SHA3,
            "ADDRESS" => Opcode::ADDRESS,
            "BALANCE" => Opcode::BALANCE,
            "SELFBALANCE" => Opcode::SELFBALANCE,
            "ORIGIN" => Opcode::ORIGIN,
            "CALLER" => Opcode::CALLER,
            "CALLVALUE" => Opcode::CALLVALUE,
            "GASPRICE" => Opcode::GASPRICE,
            "EXTCODESIZE" => Opcode::EXTCODESIZE,
            "EXTCODECOPY" => Opcode::EXTCODECOPY,
            "EXTCODEHASH" => Opcode::EXTCODEHASH,
            "RETURNDATASIZE" => Opcode::RETURNDATASIZE,
            "RETURNDATACOPY" => Opcode::RETURNDATACOPY,
            "BLOCKHASH" => Opcode::BLOCKHASH,
            "COINBASE" => Opcode::COINBASE,
            "TIMESTAMP" => Opcode::TIMESTAMP,
            "NUMBER" => Opcode::NUMBER,
            "DIFFICULTY" => Opcode::DIFFICULTY,
            "GASLIMIT" => Opcode::GASLIMIT,
            "SLOAD" => Opcode::SLOAD,
            "SSTORE" => Opcode::SSTORE,
            "GAS" => Opcode::GAS,
            "LOG0" => Opcode::LOG0,
            "LOG1" => Opcode::LOG1,
            "LOG2" => Opcode::LOG2,
            "LOG3" => Opcode::LOG3,
            "LOG4" => Opcode::LOG4,
            "CREATE" => Opcode::CREATE,
            "CREATE2" => Opcode::CREATE2,
            "CALL" => Opcode::CALL,
            "CALLCODE" => Opcode::CALLCODE,
            "DELEGATECALL" => Opcode::DELEGATECALL,
            "STATICCALL" => Opcode::STATICCALL,
            "SUICIDE" => Opcode::SUICIDE,
            "CHAINID" => Opcode::CHAINID,
            _ => return Err(Error::OpcodeParsing),
        })
    }
}
