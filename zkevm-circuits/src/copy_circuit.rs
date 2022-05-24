//! The copy circuit implementation.

use crate::copy_table::CopyTable;
// use eth_types::{Address, Field};
// use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
// use halo2_proofs::{
//     circuit::{Layouter, SimpleFloorPlanner},
//     plonk::{
//         Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, VirtualCells,
//     },
//     poly::Rotation,
// };

/// Config for StateCircuit
#[derive(Clone)]
pub struct StateConfig<F: Field> {
    copy_table: CopyTable,
    // is_memory: IsZeroConfig<F>,
//     is_bytecode: IsZeroConfig<F>,
//     is_tx_calldata: IsZeroConfig<F>,
//     is_tx_log: IsZeroConfig<F>,
}
