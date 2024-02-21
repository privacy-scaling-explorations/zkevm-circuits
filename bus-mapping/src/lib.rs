#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
// We want to have UPPERCASE indents sometimes.
#![allow(non_snake_case)]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
//#![deny(unsafe_code)] Allowed now until we find a
// better way to handle downcasting from Operation into it's variants.
#![allow(clippy::upper_case_acronyms)] // Too pedantic
#![feature(type_changing_struct_update)]

#[cfg(all(target_arch = "wasm32", feature = "notwasm"))]
compile_error!("bus-mapping: notwasm feature must be disabled when target arch is wasm");
#[cfg(all(not(target_arch = "wasm32"), not(feature = "notwasm")))]
compile_error!("bus-mapping: notwasm feature must be enabled when target arch is not wasm");

extern crate alloc;
extern crate core;

pub mod circuit_input_builder;
pub mod error;
pub mod evm;
pub mod exec_trace;
pub(crate) mod geth_errors;
pub mod mock;
pub mod operation;
pub mod precompile;
pub mod rpc;
pub mod state_db;
pub use error::Error;
