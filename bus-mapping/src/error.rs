//! Error module for the bus-mapping crate

use core::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error as StdError;

/// Error type for any BusMapping related failure.
#[derive(Debug, Copy, Clone)]
pub enum Error {
    /// Error while parsing an `Instruction/Opcode`.
    OpcodeParsing,
    /// Error while parsing a `MemoryAddress`.
    MemAddressParsing,
    /// Error while parsing a `StackAddress`.
    StackAddressParsing,
    /// Error while parsing an `EvmWord`.
    EvmWordParsing,
    /// Error while trying to convert to an incorrect `OpcodeId`.
    InvalidOpConversion,
    /// Serde de/serialization error.
    SerdeError,
    /// Error while trying to access an invalid/empty Stack location.
    InvalidStackPointer,
    /// Error while trying to access an invalid/empty Memory location.
    InvalidMemoryPointer,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}
