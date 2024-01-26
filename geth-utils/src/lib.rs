//! Connection to external EVM tracer.

pub mod block;
pub mod mpt;

pub use block::*;
pub use mpt::*;

mod go {
    use std::os::raw::c_char;
    extern "C" {
        pub fn CreateTrace(str: *const c_char) -> *const c_char;
        pub fn GetWitness(str: *const c_char) -> *const c_char;
        pub fn FreeString(str: *const c_char);
    }
}
