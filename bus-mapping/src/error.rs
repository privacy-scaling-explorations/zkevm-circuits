//! Error module for the bus-mapping crate

use core::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error as StdError;

#[derive(Debug, Copy, Clone)]
pub(crate) enum Error {
    OpcodeParsing,
    MemAddressParsing,
    EvmWordParsing,
    InvalidOpConversion,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}
