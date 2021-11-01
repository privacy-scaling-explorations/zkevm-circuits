//! Error module for the bus-mapping crate

use core::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error as StdError;

/// Error type for a failure while parsig an EVM word as returned by geth in the json-serialized
/// trace.
#[derive(Debug)]
pub enum EvmWordParsingError {
    /// Hex string containing the EVM word is greater than 32*2
    TooLong,
    /// Hex decoding error
    Hex(hex::FromHexError),
}

/// Error type for any BusMapping related failure.
#[derive(Debug)]
pub enum Error {
    /// Error while parsing an `Instruction/Opcode`.
    OpcodeParsing,
    /// Error while parsing a `MemoryAddress`.
    MemAddressParsing,
    /// Error while parsing a `StackAddress`.
    StackAddressParsing,
    /// Error while parsing an `EvmWord`.
    EvmWordParsing(EvmWordParsingError),
    /// Error while trying to convert to an incorrect `OpcodeId`.
    InvalidOpConversion,
    /// Serde de/serialization error.
    SerdeError(serde_json::error::Error),
    /// Error while trying to access an invalid/empty Stack location.
    InvalidStackPointer,
    /// Error while trying to access an invalid/empty Memory location.
    InvalidMemoryPointer,
    /// Error while trying to access an invalid/empty Storage key.
    InvalidStorageKey,
    /// Error when an EvmWord is too big to be converted into a `MemoryAddress`.
    WordToMemAddr,
    /// Error while generating a trace.
    TracingError,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}

impl From<EvmWordParsingError> for Error {
    fn from(err: EvmWordParsingError) -> Self {
        Error::EvmWordParsing(err)
    }
}

/// Error type for a failure while parsig an Ethereum Address.
#[derive(Debug)]
pub enum EthAddressParsingError {
    /// Hex string containing the Ethereum Address is not 20*2 characters
    BadLength,
    /// Hex decoding error
    Hex(hex::FromHexError),
}
