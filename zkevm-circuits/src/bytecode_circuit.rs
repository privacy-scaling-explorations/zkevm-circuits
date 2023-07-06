//! The bytecode circuit implementation.

/// Bytecode unroller
pub mod bytecode_unroller;
/// Bytecode circuit
pub mod circuit;
pub(crate) mod param;

#[cfg(any(test, feature = "test-circuits"))]
mod dev;
/// Bytecode circuit tester
#[cfg(test)]
mod test;
#[cfg(feature = "test-circuits")]
pub use dev::BytecodeCircuit as TestBytecodeCircuit;
