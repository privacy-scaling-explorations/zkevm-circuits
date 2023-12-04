pub use crate::util::{
    query_expression,
    word::{Word, WordExpr},
    Challenges, Expr,
};
use crate::{
    Table,
    evm_circuit::{
        param::{
            LOOKUP_CONFIG, N_BYTES_MEMORY_ADDRESS, N_COPY_COLUMNS, N_PHASE2_COLUMNS, N_U8_LOOKUPS,
        },
    },
    util::{cell_manager::CMFixedWidthStrategyDistribution, int_decomposition::IntDecomposition},
    witness::{Block, ExecStep, Rw, RwMap},
};
use eth_types::{Address, Field, U256};
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};
use itertools::Itertools;
use std::hash::{Hash, Hasher};

pub(crate) mod common_gadget;
pub(crate) mod constraint_builder;
pub(crate) mod instrumentation;
pub(crate) mod math_gadget;
pub(crate) mod memory_gadget;

pub use gadgets::util::{and, not, or, select, sum};

use super::param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_U64, N_U16_LOOKUPS};

#[deprecated(note = "Removing this would require to edit almost all gadget")]
pub(crate) use crate::util::cell_manager::{Cell, CellType};

pub use crate::util::*;

//
#[allow(clippy::mut_range_bound)]
pub(crate) fn evm_cm_distribute_advice<F: Field>(
    meta: &mut ConstraintSystem<F>,
    advices: &[Column<Advice>],
) -> CMFixedWidthStrategyDistribution {
    let mut dist = CMFixedWidthStrategyDistribution::default();

    let mut column_idx = 0;
    // Mark columns used for lookups in Phase3
    for &(table, count) in LOOKUP_CONFIG {
        for _ in 0usize..count {
            dist.add(CellType::Lookup(table), advices[column_idx]);
            column_idx += 1;
        }
    }

    // Mark columns used for Phase2 constraints
    for _ in 0..N_PHASE2_COLUMNS {
        dist.add(CellType::StoragePhase2, advices[column_idx]);
        column_idx += 1;
    }

    // Mark columns used for copy constraints
    for _ in 0..N_COPY_COLUMNS {
        meta.enable_equality(advices[column_idx]);
        dist.add(CellType::StoragePermutation, advices[column_idx]);
        column_idx += 1;
    }

    // Mark columns used for byte lookup
    #[allow(clippy::reversed_empty_ranges)]
    for _ in 0..N_U8_LOOKUPS {
        dist.add(CellType::Lookup(Table::U8), advices[column_idx]);
        assert_eq!(advices[column_idx].column_type().phase(), 0);
        column_idx += 1;
    }

    // Mark columns used for byte lookup
    #[allow(clippy::reversed_empty_ranges)]
    for _ in 0..N_U16_LOOKUPS {
        dist.add(CellType::Lookup(Table::U16), advices[column_idx]);
        assert_eq!(advices[column_idx].column_type().phase(), 0);
        column_idx += 1;
    }

    // Mark columns used for for Phase1 constraints
    for _ in column_idx..advices.len() {
        dist.add(CellType::StoragePhase1, advices[column_idx]);
        column_idx += 1;
    }

    dist
}

#[derive(Clone, Debug)]
pub struct RandomLinearCombination<F, const N: usize> {
    // random linear combination expression of cells
    expression: Expression<F>,
    // inner cells in little-endian for synthesis
    pub(crate) cells: [Cell<F>; N],
}

impl<F: Field, const N: usize> RandomLinearCombination<F, N> {
    /// XXX for randomness 256.expr(), consider using IntDecomposition instead
    pub(crate) fn new(cells: [Cell<F>; N], randomness: Expression<F>) -> Self {
        Self {
            expression: rlc::expr(&cells.clone().map(|cell| cell.expr()), randomness),
            cells,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: Option<[u8; N]>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        bytes.map_or(Err(Error::Synthesis), |bytes| {
            self.cells
                .iter()
                .zip(bytes.iter())
                .map(|(cell, byte)| {
                    cell.assign(region, offset, Value::known(F::from(*byte as u64)))
                })
                .collect()
        })
    }
}

impl<F: Field, const N: usize> Expr<F> for RandomLinearCombination<F, N> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

pub(crate) type MemoryAddress<F> = IntDecomposition<F, N_BYTES_MEMORY_ADDRESS>;

pub(crate) type AccountAddress<F> = IntDecomposition<F, N_BYTES_ACCOUNT_ADDRESS>;

pub(crate) type U64Cell<F> = IntDecomposition<F, N_BYTES_U64>;

pub(crate) fn is_precompiled(address: &Address) -> bool {
    address.0[0..19] == [0u8; 19] && (1..=9).contains(&address.0[19])
}

const BASE_128_BYTES: [u8; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

/// convert address (h160) to single expression.
pub fn address_word_to_expr<F: Field>(address: Word<Expression<F>>) -> Expression<F> {
    address.lo() + address.hi() * Expression::Constant(F::from_repr(BASE_128_BYTES).unwrap())
}

/// Helper struct to read rw operations from a step sequentially.
pub(crate) struct StepRws<'a> {
    rws: &'a RwMap,
    step: &'a ExecStep,
    offset: usize,
}

impl<'a> StepRws<'a> {
    /// Create a new StateRws by taking the reference to a block and the step.
    pub(crate) fn new<F>(block: &'a Block<F>, step: &'a ExecStep) -> Self {
        Self {
            rws: &block.rws,
            step,
            offset: 0,
        }
    }
    /// Increment the step rw operation offset by `inc`.
    pub(crate) fn offset_add(&mut self, inc: usize) {
        self.offset += inc
    }
    /// Return the next rw operation from the step.
    pub(crate) fn next(&mut self) -> Rw {
        let rw = self.rws[self.step.rw_index(self.offset)];
        self.offset += 1;
        rw
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::evm_circuit::param::STEP_WIDTH;

    use super::*;

    #[test]
    fn test_evm_cm_distribute_advice_1() {
        let mut cs = ConstraintSystem::<Fr>::default();
        let advices = vec![cs.advice_column(); STEP_WIDTH];

        let cm = evm_cm_distribute_advice(&mut cs, &advices);

        let lookup_config_size = LOOKUP_CONFIG
            .iter()
            .map(|(_, size)| size.to_owned())
            .sum::<usize>();

        assert_eq!(
            cm.get(CellType::StoragePhase1).unwrap().len(),
            STEP_WIDTH
                - N_PHASE2_COLUMNS
                - N_COPY_COLUMNS
                - lookup_config_size
                - N_U8_LOOKUPS
                - N_U16_LOOKUPS
        );
        assert_eq!(
            cm.get(CellType::StoragePhase2).unwrap().len(),
            N_PHASE2_COLUMNS
        );
        assert_eq!(
            cm.get(CellType::StoragePermutation).unwrap().len(),
            N_COPY_COLUMNS
        );

        // CellType::Lookup
        for &(table, count) in LOOKUP_CONFIG {
            assert_eq!(cm.get(CellType::Lookup(table)).unwrap().len(), count);
        }
        assert_eq!(
            cm.get(CellType::Lookup(Table::U8)).unwrap().len(),
            N_U8_LOOKUPS
        );
        if N_U16_LOOKUPS == 0 {
            assert!(cm.get(CellType::Lookup(Table::U16)).is_none());
        } else {
            assert_eq!(
                cm.get(CellType::Lookup(Table::U16)).unwrap().len(),
                N_U16_LOOKUPS
            );
        }
    }
}
