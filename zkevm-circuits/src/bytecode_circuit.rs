//! The bytecode circuit implementation.

/// Bytecode unroller
pub mod bytecode_unroller;
/// Bytecode circuit
pub mod circuit;
pub(crate) mod param;
/// Bytecode circuit tester
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
pub mod test;
pub use test::BytecodeCircuit as TestBytecodeCircuit;
