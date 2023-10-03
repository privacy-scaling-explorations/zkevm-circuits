//! # zk_evm

// We should try not to use incomplete_features unless it is really really needed and cannot be
// avoided like `adt_const_params` used by DummyGadget
#![allow(incomplete_features)]
// Needed by DummyGadget in evm circuit
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

pub mod bytecode_circuit;
#[allow(dead_code, reason = "under active development")]
pub mod circuit_tools;
pub mod copy_circuit;
pub mod evm_circuit;
pub mod exp_circuit;
pub mod keccak_circuit;
#[allow(dead_code, reason = "under active development")]
pub mod mpt_circuit;
pub mod permutation_circuit;
pub mod pi_circuit;
pub mod root_circuit;
pub mod state_circuit;
pub mod super_circuit;
pub mod table;

#[cfg(any(test, feature = "test-util"))]
pub mod test_util;

pub mod instance;
pub mod tx_circuit;
pub mod util;
pub mod witness;

pub use gadgets::impl_expr;
