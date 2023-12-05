//! # zk_evm

// We should try not to use incomplete_features unless it is really really needed and cannot be
// avoided like `adt_const_params` used by DummyGadget
#![allow(incomplete_features)]
// Needed by DummyGadget in evm circuit
#![cfg(not(feature = "js"))]
#![feature(adt_const_params)]
// Required for adding reasons in allow(dead_code)
#![feature(lint_reasons)]
// Needed by some builder patterns in testing modules.
#![cfg_attr(docsrs, feature(doc_cfg))]
// We want to have UPPERCASE idents sometimes.
#![allow(clippy::upper_case_acronyms)]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![deny(unsafe_code)]
#![deny(clippy::debug_assert_with_mut_call)]

#[cfg(not(feature = "js"))]
pub mod bytecode_circuit;

#[allow(dead_code)]
pub mod circuit_tools;

#[cfg(not(feature = "js"))]
pub mod copy_circuit;

#[cfg(not(feature = "js"))]
pub mod evm_circuit;

#[cfg(not(feature = "js"))]
pub mod exp_circuit;

#[cfg(not(feature = "js"))]
pub mod keccak_circuit;

pub mod mpt_circuit;

#[cfg(not(feature = "js"))]
pub mod pi_circuit;

#[cfg(not(feature = "js"))]
pub mod root_circuit;

#[cfg(not(feature = "js"))]
pub mod state_circuit;

#[cfg(not(feature = "js"))]
pub mod super_circuit;

pub mod table;

#[cfg(not(feature = "js"))]
#[cfg(any(test, feature = "test-util"))]
pub mod test_util;

#[cfg(not(feature = "js"))]
pub mod instance;

#[cfg(not(feature = "js"))]
pub mod tx_circuit;

pub mod util;

pub mod witness;

pub use gadgets::impl_expr;
use strum_macros::EnumIter;

///
pub mod param;


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter)]
/// Each item represents the lookup table to query
pub enum Table {
    /// The range check table for u8
    U8,
    /// The range check table for u16
    U16,
    /// The rest of the fixed table. See [`FixedTableTag`]
    Fixed,
    /// Lookup for transactions
    Tx,
    /// Lookup for read write operations
    Rw,
    /// Lookup for bytecode table
    Bytecode,
    /// Lookup for block constants
    Block,
    /// Lookup for copy table
    Copy,
    /// Lookup for keccak table
    Keccak,
    /// Lookup for exp table
    Exp,
}