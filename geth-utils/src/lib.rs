//! Connection to external EVM tracer.

pub mod mpt;
pub mod block;

pub use mpt::*;
pub use block::*;

mod go {
    use std::os::raw::c_char;
    extern "C" {
        pub fn CreateTrace(str: *const c_char) -> *const c_char;
        pub fn GetWitness(str: *const c_char) -> *const c_char;
        pub fn FreeString(str: *const c_char);
    }
}