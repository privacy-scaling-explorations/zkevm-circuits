//! The bytecode circuit implementation.

mod bytecode_chiquito;
/// Bytecode unroller
pub mod bytecode_unroller;
/// Bytecode circuit
pub mod circuit;
/// Bytecode circuit tester
#[cfg(any(feature = "test", test))]
mod test;
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
pub use dev::BytecodeCircuit as TestBytecodeCircuit;

/// Bytecode circuit tester
#[cfg(any(feature = "test", test))]
pub mod dev;
pub(crate) mod param;
mod push_data_chiquito;
mod wit_gen;
