//! Lt chip can be used to compare LT for two expressions LHS and RHS.

use std::array;

use array_init::array_init;
use eth_types::Field;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, VirtualCells},
    poly::Rotation,
};

use super::{
    bool_check,
    util::{expr_from_bytes, pow_of_two},
};

/// Instruction that the Lt chip needs to implement.
pub trait LtInstruction<F: FieldExt> {
    /// Assign the lhs and rhs witnesses to the Lt chip's region.
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(), Error>;
}

/// Config for the Lt chip.
#[derive(Clone, Debug)]
pub struct LtConfig<F, const N_BYTES: usize> {
    /// Denotes the lt outcome. If lhs < rhs then lt == 1, otherwise lt == 0.
    pub lt: Column<Advice>,
    /// Denotes the bytes representation of the difference between lhs and rhs.
    pub diff: [Column<Advice>; N_BYTES],
    /// Denotes the range within which both lhs and rhs lie.
    pub range: F,
}

impl<F: Field, const N_BYTES: usize> LtConfig<F, N_BYTES> {
    /// Returns an expression that denotes whether lhs < rhs, or not.
    pub fn is_lt(&self, meta: &mut VirtualCells<F>, rotation: Option<Rotation>) -> Expression<F> {
        meta.query_advice(self.lt, rotation.unwrap_or_else(Rotation::cur))
    }
}

/// Chip that compares lhs < rhs.
#[derive(Clone, Debug)]
pub struct LtChip<F, const N_BYTES: usize> {
    config: LtConfig<F, N_BYTES>,
}

impl<F: Field, const N_BYTES: usize> LtChip<F, N_BYTES> {
    /// Configures the Lt chip.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        lhs: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        rhs: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    ) -> LtConfig<F, N_BYTES> {
        let lt = meta.advice_column();
        let diff = array_init(|_| meta.advice_column());
        let range = pow_of_two(N_BYTES * 8);

        meta.create_gate("lt gate", |meta| {
            let q_enable = q_enable(meta);
            let lt = meta.query_advice(lt, Rotation::cur());

            let diff_bytes = diff
                .iter()
                .map(|c| meta.query_advice(*c, Rotation::cur()))
                .collect::<Vec<Expression<F>>>();

            let check_a =
                lhs(meta) - rhs(meta) - expr_from_bytes(&diff_bytes) + (lt.clone() * range);

            let check_b = bool_check(lt);

            array::IntoIter::new([check_a, check_b]).map(move |poly| q_enable.clone() * poly)
        });

        LtConfig { lt, diff, range }
    }

    /// Constructs a Lt chip given a config.
    pub fn construct(config: LtConfig<F, N_BYTES>) -> LtChip<F, N_BYTES> {
        LtChip { config }
    }
}

impl<F: Field, const N_BYTES: usize> LtInstruction<F> for LtChip<F, N_BYTES> {
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(), Error> {
        let config = self.config();

        let lt = lhs < rhs;
        region.assign_advice(
            || "lt chip: lt",
            config.lt,
            offset,
            || Ok(F::from(lt as u64)),
        )?;

        let diff = (lhs - rhs) + (if lt { config.range } else { F::zero() });
        let diff_bytes = diff.to_repr();
        let diff_bytes = diff_bytes.as_ref();
        for (idx, diff_column) in config.diff.iter().enumerate() {
            region.assign_advice(
                || format!("lt chip: diff byte {}", idx),
                *diff_column,
                offset,
                || Ok(F::from(diff_bytes[idx] as u64)),
            )?;
        }

        Ok(())
    }
}

impl<F: Field, const N_BYTES: usize> Chip<F> for LtChip<F, N_BYTES> {
    type Config = LtConfig<F, N_BYTES>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
