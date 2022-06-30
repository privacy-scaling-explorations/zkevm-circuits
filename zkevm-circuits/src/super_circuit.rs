//! Mario Kart: Super Circuit
//! ⠀⠀⠀⠀⠀⠀⠀⢀⣀⣀⡀⠀⠀⠀⠀⠀⠀⠀
//! ⠀⠀⠀⠀⡠⣴⣮⣷⣶⡶⣾⣽⣶⢤⡀⠀⠀⠀
//! ⠀⠀⢠⣾⣿⢧⣾⣿⣿⣧⣿⣿⣿⣷⡱⡄⠀⠀
//! ⠀⣠⣿⣿⣯⣿⣿⣿⣿⡿⣼⣻⠿⠟⠛⠻⢦⡀
//! ⡼⠁⢿⣟⣎⣿⣿⠿⠟⠃⠉⠀⠀⠀⠀⠀⠀⣷
//! ⢳⡀⠀⠀⠀⠀⠀⠀⠀⣀⡠⡤⢲⣾⡏⢱⡠⠃
//! ⠀⠉⠲⡲⠒⠒⡖⠚⠿⢿⠃⠡⡀⠉⢁⠞⠀⠀
//! ⠀⠀⠀⠘⠳⢄⣘⢤⣀⠈⢂⣤⠴⠚⠁⠀⠀⠀
//! ⠀⠀⠀⠀⠀⠀⠀⠉⠉⠉⠁⠀⠀⠀⠀⠀⠀⠀

#![allow(missing_docs)]
use halo2_proofs::{circuit::Layouter, plonk::*};

use crate::evm_circuit::EvmCircuit;
use crate::tx_circuit::TxCircuit;

use crate::{
    evm_circuit::witness::{BlockContext, Bytecode, RwMap, Transaction},
    rw_table::RwTable,
};

#[derive(Clone)]
pub struct SuperCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    tx_table: [Column<Advice>; 4],
    rw_table: RwTable,
    bytecode_table: [Column<Advice>; 5],
    block_table: [Column<Advice>; 3],
    evm_circuit: EvmCircuit<F>,
    tx_circuit: TxCircuit<F, MAX_TXS, MAX_CALLDATA>,
}

#[cfg(test)]
mod super_circuit_tests {}
