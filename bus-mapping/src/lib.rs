//! Crate docs

#![cfg_attr(docsrs, feature(doc_cfg))]
// Temporary until we have more of the crate implemented.
#![allow(dead_code)]
// Catch documentation errors caused by code changes.
#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
//#![deny(unsafe_code)]

extern crate alloc;
mod error;
mod evm;
mod exec_trace;
mod operation;
