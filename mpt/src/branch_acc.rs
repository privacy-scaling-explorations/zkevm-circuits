use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::{marker::PhantomData, u64};

use crate::param::HASH_WIDTH;

#[derive(Clone, Debug)]
pub(crate) struct BranchAccConfig {
    range_table: Column<Fixed>,
    advices: [Column<Advice>; HASH_WIDTH],
}

// BranchAccChip verifies the random linear combination for the branch.
pub(crate) struct BranchAccChip<F> {
    config: BranchAccConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchAccChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        branch_acc_r: F,
        rlp2: Column<Advice>,
        advices: [Column<Advice>; HASH_WIDTH],
        branch_acc: Column<Advice>,
        branch_mult: Column<Advice>,
    ) -> BranchAccConfig {
        let range_table = meta.fixed_column();

        let config = BranchAccConfig {
            range_table,
            advices,
        };

        meta.create_gate("branch acc", |meta| {
            let q_enable = q_enable(meta);

            let mut constraints = vec![];
            let rlp2 = meta.query_advice(rlp2, Rotation::cur());
            let branch_acc_prev =
                meta.query_advice(branch_acc, Rotation::prev());
            let branch_acc_cur = meta.query_advice(branch_acc, Rotation::cur());
            let branch_mult_prev =
                meta.query_advice(branch_mult, Rotation::prev());
            let branch_mult_cur =
                meta.query_advice(branch_mult, Rotation::cur());

            let c128 = Expression::Constant(F::from_u64(128 as u64));
            let c160 = Expression::Constant(F::from_u64(160 as u64));

            // empty:
            // branch_acc_curr = branch_acc_prev + 128 * branch_mult_prev
            constraints.push((
                "branch acc empty",
                q_enable.clone()
                    * (c160.clone() - rlp2.clone()) // rlp2 is 160 when non-empty and 0 when empty (field modulus is not divisible by 160, so this should be secure)
                    * (branch_acc_cur.clone()
                        - branch_acc_prev.clone()
                        - c128.clone() * branch_mult_prev.clone()),
            ));
            constraints.push((
                "branch acc mult empty",
                q_enable.clone()
                    * (c160.clone() - rlp2.clone()) // rlp2 is 160 when non-empty and 0 when empty (field modulus is not divisible by 160, so this should be secure)
                    * (branch_mult_cur.clone()
                        - branch_mult_prev.clone() * branch_acc_r),
            ));

            // non-empty
            let mut curr_r = branch_mult_prev.clone();
            let mut expr = c160.clone() * curr_r.clone();
            curr_r = curr_r * branch_acc_r;
            for col in advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());

                expr = expr + s * curr_r.clone();
                curr_r = curr_r * branch_acc_r;
            }
            constraints.push((
                "branch acc non-empty",
                q_enable.clone()
                    * rlp2.clone() // rlp2 is 0 when empty and 160 when non-empty (field modulus is not divisible by 160, so this should be secure)
                    * (branch_acc_cur.clone() - branch_acc_prev.clone() - expr),
            ));
            constraints.push((
                "branch acc mult non-empty",
                q_enable.clone()
                    * rlp2.clone() // rlp2 is 0 when empty and 160 when non-empty (field modulus is not divisible by 160, so this should be secure)
                    * (branch_mult_cur.clone() - curr_r),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: BranchAccConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchAccChip<F> {
    type Config = BranchAccConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
