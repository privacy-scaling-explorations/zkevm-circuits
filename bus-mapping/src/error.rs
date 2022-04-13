//! Error module for the bus-mapping crate

use core::fmt::{Display, Formatter, Result as FmtResult};
use eth_types::{Address, GethExecStep, Word, H256};
use ethers_providers::ProviderError;
use std::error::Error as StdError;

/// Error type for any BusMapping related failure.
#[derive(Debug)]
pub enum Error {
    /// Serde de/serialization error.
    SerdeError(serde_json::error::Error),
    /// JSON-RPC related error.
    JSONRpcError(ProviderError),
    /// OpcodeId is not a call type.
    OpcodeIdNotCallType,
    /// Account not found in the StateDB
    AccountNotFound(Address),
    /// Storage key not found in the StateDB
    StorageKeyNotFound(Address, Word),
    /// Code not found in the CodeDB
    CodeNotFound(H256),
    /// Unable to figure out error at a [`GethExecStep`]
    UnexpectedExecStepError(&'static str, GethExecStep),
    /// Invalid [`eth_types::GethExecTrace`] due to an invalid/unexpected value
    /// in it.
    InvalidGethExecTrace(&'static str),
    /// Invalid [`GethExecStep`] due to an invalid/unexpected value in it.
    InvalidGethExecStep(&'static str, GethExecStep),
    /// Eth type related error.
    EthTypeError(eth_types::Error),
    /// EVM Execution error
    ExecutionError(ExecError),
}

impl From<eth_types::Error> for Error {
    fn from(err: eth_types::Error) -> Self {
        Error::EthTypeError(err)
    }
}

impl From<ProviderError> for Error {
    fn from(err: ProviderError) -> Self {
        Error::JSONRpcError(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}

/// EVM Execution Error
#[derive(Clone, Debug, PartialEq)]
pub enum ExecError {
    /// Invalid Opcode
    InvalidOpcode,
    /// For opcodes who push more than pop
    StackOverflow,
    /// For opcodes which pop, DUP and SWAP, which peek deeper element directly
    StackUnderflow,
    /// Out of Gas
    OutOfGas(OogError),
    /// For SSTORE, LOG0, LOG1, LOG2, LOG3, LOG4, CREATE, CALL, CREATE2,
    /// SELFDESTRUCT
    WriteProtection,
    /// For CALL, CALLCODE, DELEGATECALL, STATICCALL
    Depth,
    /// For CALL, CALLCODE
    InsufficientBalance,
    /// For CREATE, CREATE2
    ContractAddressCollision,
    /// contract must not begin with 0xef due to EIP #3541 EVM Object Format
    /// (EOF)
    InvalidCreationCode,
    /// For JUMP, JUMPI
    InvalidJump,
    /// For RETURNDATACOPY
    ReturnDataOutOfBounds,
    /// For RETURN in a CREATE, CREATE2
    CodeStoreOutOfGas,
    /// For RETURN in a CREATE, CREATE2
    MaxCodeSizeExceeded,
}

/// Out of Gas errors by opcode
#[derive(Clone, Debug, PartialEq)]
pub enum OogError {
    /// Out of Gas for opcodes which have non-zero constant gas cost
    Constant,
    /// Out of Gas for MLOAD, MSTORE, MSTORE8, which have static memory
    /// expansion gas cost
    StaticMemoryExpansion,
    /// Out of Gas for CREATE, RETURN, REVERT, which have dynamic memory
    /// expansion gas cost
    DynamicMemoryExpansion,
    /// Out of Gas for CALLDATACOPY, CODECOPY, RETURNDATACOPY, which copy a
    /// specified chunk of memory
    MemoryCopy,
    /// Out of Gas for BALANCE, EXTCODESIZE, EXTCODEHASH, which possibly touch
    /// an extra account
    AccountAccess,
    /// Out of Gas for RETURN which has code storing gas cost when it's is
    /// creation
    CodeStore,
    /// Out of Gas for LOG0, LOG1, LOG2, LOG3, LOG4
    Log,
    /// Out of Gas for EXP
    Exp,
    /// Out of Gas for SHA3
    Sha3,
    /// Out of Gas for EXTCODECOPY
    ExtCodeCopy,
    /// Out of Gas for SLOAD
    Sload,
    /// Out of Gas for SSTORE
    Sstore,
    /// Out of Gas for CALL
    Call,
    /// Out of Gas for CALLCODE
    CallCode,
    /// Out of Gas for DELEGATECALL
    DelegateCall,
    /// Out of Gas for CREATE2
    Create2,
    /// Out of Gas for STATICCALL
    StaticCall,
    /// Out of Gas for SELFDESTRUCT
    SelfDestruct,
}
