//! The bytecode circuit implementation.

/// Bytecode unroller
pub mod bytecode_unroller;
pub(crate) mod param;
/// bytecode circuit test
#[cfg(any(feature = "test", test))]
mod test;
pub use test::BytecodeCircuit;
