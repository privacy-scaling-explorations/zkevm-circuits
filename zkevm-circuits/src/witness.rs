//! Witness for all circuits.
//! The `Block<F>` is the witness struct post-processed from geth traces and
//! used to generate witnesses for circuits.

mod block;
pub use block::{block_convert, Block, BlockContext};
mod bytecode;
pub use bytecode::{BytecodeCollection, BytecodeUnroller as Bytecode};
mod mpt;
pub use mpt::{MptUpdate, MptUpdateRow, MptUpdates};
mod rw;
pub use bus_mapping::circuit_input_builder::{Call, ExecStep, Transaction};
pub use rw::{Rw, RwMap, RwRow};
