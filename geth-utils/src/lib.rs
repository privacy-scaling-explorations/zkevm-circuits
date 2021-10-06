//! Connection to external EVM tracer.

use core::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error as StdError;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

extern "C" {
    fn CreateTrace(config: GoString) -> *const c_char;
}

/// A Go string.
#[repr(C)]
struct GoString {
    a: *const c_char,
    b: i64,
}

/// Creates the trace
pub fn trace(config: &str) -> Result<String, Error> {
    let c_config = CString::new(config).expect("invalid config");
    let go_config = to_go_string(&c_config);
    let result = unsafe { CreateTrace(go_config) };
    let c_str = unsafe { CStr::from_ptr(result) };
    let string = c_str
        .to_str()
        .expect("Error translating EVM trace from library");
    match string.is_empty() || string.starts_with("Error") {
        true => Err(Error::TracingError),
        false => Ok(string.to_string()),
    }
}

fn to_go_string(data: &CString) -> GoString {
    let ptr = data.as_ptr();
    GoString {
        a: ptr,
        b: data.as_bytes().len() as i64,
    }
}

/// Error type for any geth-utils related failure.
#[derive(Debug, Copy, Clone)]
pub enum Error {
    /// Error while tracing.
    TracingError,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}
