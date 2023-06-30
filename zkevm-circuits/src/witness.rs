//! Witness for all circuits.
//! The `Block<F>` is the witness struct post-processed from geth traces and
//! used to generate witnesses for circuits.

mod block;
pub use block::{block_convert, Block, BlockContext};
mod bytecode;
pub use bytecode::Bytecode;
mod mpt;
pub use mpt::{MptUpdate, MptUpdateRow, MptUpdates};
mod rw;
pub use bus_mapping::circuit_input_builder::ExecStep;
pub use rw::{Rw, RwMap, RwRow};
mod tx;
pub use bus_mapping::circuit_input_builder::Call;
pub use tx::Transaction;
mod taiko;
pub use taiko::Taiko;
