use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::{marker::PhantomData, u64};

use crate::param::{HASH_WIDTH, R_TABLE_LEN};

#[derive(Clone, Debug)]
pub(crate) struct BranchAccConfig {}

// BranchAccChip verifies the random linear combination for the branch.
pub(crate) struct BranchAccChip<F> {
    config: BranchAccConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchAccChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        rlp2: Column<Advice>,
        advices: [Column<Advice>; HASH_WIDTH],
        branch_acc: Column<Advice>,
        branch_mult: Column<Advice>,
        r_table: Vec<Expression<F>>,
    ) -> BranchAccConfig {
        let config = BranchAccConfig {};

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
                    * (c160.clone() - rlp2.clone())
                    * (branch_acc_cur.clone()
                        - branch_acc_prev.clone()
                        - c128.clone() * branch_mult_prev.clone()),
            ));
            constraints.push((
                "branch acc mult empty",
                q_enable.clone()
                    * (c160.clone() - rlp2.clone())
                    * (branch_mult_cur.clone()
                        - branch_mult_prev.clone() * r_table[0].clone()),
            ));

            // non-empty
            let mut expr = c160.clone() * branch_mult_prev.clone();
            for (ind, col) in advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                expr =
                    expr + s * branch_mult_prev.clone() * r_table[ind].clone();
            }
            constraints.push((
                "branch acc non-empty",
                q_enable.clone()
                    * rlp2.clone()
                    * (branch_acc_cur.clone() - branch_acc_prev.clone() - expr),
            ));
            constraints.push((
                "branch acc mult non-empty",
                q_enable.clone()
                    * rlp2.clone()
                    * (branch_mult_cur.clone()
                        - branch_mult_prev.clone()
                            * r_table[R_TABLE_LEN - 1].clone()
                            * r_table[0].clone()),
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
