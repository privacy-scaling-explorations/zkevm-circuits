use std::default;

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    plonk::{Circuit, ConstraintSystem, Advice, Fixed, Column, FirstPhase, Challenge, Error, SecondPhase, Selector, Expression}, 
    circuit::{SimpleFloorPlanner, Layouter, layouter, Value},
    poly::Rotation,
};

use crate::circuit_tools::{memory::{Memory}, constraint_builder::ConstraintBuilder, cell_manager::{CellManager, CellType}};

const MAX_DEG: usize = 5;

#[derive(Clone)]
pub struct RlpConfig {
    pub(crate) sel: Selector,
    pub(crate) bytes: Column<Advice>,
    pub(crate) rlc: Column<Advice>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RlpCell {
    PhaseOne,
    PhaseTwo,
    Stack,
    Byte,
}

impl CellType for RlpCell {
    fn byte_type() -> Option<Self> {
        Some(RlpCell::Byte)
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            1 => RlpCell::PhaseOne,
            2 => RlpCell::PhaseTwo,
            _ => unreachable!()
        }
    }
}

impl Default for RlpCell {
    fn default() -> Self {
        RlpCell::PhaseOne
    }
}

impl RlpConfig {
    pub fn new<F: Field>(
        meta: &mut ConstraintSystem<F>, 
        gamma: Challenge,
        sigma: Challenge,
    ) -> Self {
        let sel = meta.selector();
        let bytes = meta.advice_column();
        let rlc = meta.advice_column();

        let memory = Memory::new(
            meta,
            vec![(RlpCell::Stack, 2)],
            0,
            5
        );
        let cm = CellManager::new(
            meta,
            vec![
                (RlpCell::PhaseOne, 3, 1, false),
                (RlpCell::PhaseTwo, 3, 2, false),
            ],
            0,
            5,
        );
        let mut cb =  ConstraintBuilder::new(MAX_DEG,  Some(cm), None);
        todo!()
    }
}
