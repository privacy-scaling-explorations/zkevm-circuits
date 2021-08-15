//! Error module for the bus-mapping crate

use core::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error as StdError;

#[derive(Debug, Copy, Clone)]
pub enum Error {
    OpcodeParsing,
    MemAddressParsing,
    EvmWordParsing,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}
