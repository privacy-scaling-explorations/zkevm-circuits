//! Witness for all circuits.
//! The `Block<F>` is the witness struct post-processed from geth traces and
//! used to generate witnesses for circuits.

#[cfg(not(feature = "js"))]
mod block;

#[cfg(not(feature = "js"))]
pub use block::{block_convert, Block, BlockContext};

mod mpt;
pub use mpt::{MptUpdate, MptUpdateRow, MptUpdates};

#[cfg(not(feature = "js"))]
mod rw;

#[cfg(not(feature = "js"))]
pub use bus_mapping::circuit_input_builder::{Call, ExecStep, Transaction, Withdrawal};

#[cfg(not(feature = "js"))]
pub use rw::{Rw, RwMap, RwRow};
