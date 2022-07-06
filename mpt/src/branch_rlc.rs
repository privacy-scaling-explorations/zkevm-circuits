use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{HASH_WIDTH, R_TABLE_LEN};

#[derive(Clone, Debug)]
pub(crate) struct BranchRLCConfig {}

// BranchRLCChip verifies the random linear combination for the branch which is
// then used to check the hash of a branch.
pub(crate) struct BranchRLCChip<F> {
    config: BranchRLCConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchRLCChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        rlp2: Column<Advice>,
        advices: [Column<Advice>; HASH_WIDTH],
        branch_acc: Column<Advice>,
        branch_mult: Column<Advice>,
        is_node_hashed: Column<Advice>,
        r_table: Vec<Expression<F>>,
    ) -> BranchRLCConfig {
        let config = BranchRLCConfig {};

        meta.create_gate("branch acc", |meta| {
            let q_enable = q_enable(meta);

            let mut constraints = vec![];
            let rlp2 = meta.query_advice(rlp2, Rotation::cur());
            let branch_acc_prev = meta.query_advice(branch_acc, Rotation::prev());
            let branch_acc_cur = meta.query_advice(branch_acc, Rotation::cur());
            let branch_mult_prev = meta.query_advice(branch_mult, Rotation::prev());
            let branch_mult_cur = meta.query_advice(branch_mult, Rotation::cur());

            let is_node_hashed = meta.query_advice(is_node_hashed, Rotation::cur());

            let one = Expression::Constant(F::one());
            let c128 = Expression::Constant(F::from(128_u64));
            let c160 = Expression::Constant(F::from(160_u64));

            // empty:
            // branch_acc_curr = branch_acc_prev + 128 * branch_mult_prev
            constraints.push((
                "branch acc empty",
                q_enable.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * (c160.clone() - rlp2.clone())
                    * (branch_acc_cur.clone()
                        - branch_acc_prev.clone()
                        - c128 * branch_mult_prev.clone()),
            ));
            constraints.push((
                "branch acc mult empty",
                q_enable.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * (c160.clone() - rlp2.clone())
                    * (branch_mult_cur.clone() - branch_mult_prev.clone() * r_table[0].clone()),
            ));

            // non-empty
            let mut expr = c160 * branch_mult_prev.clone();
            for (ind, col) in advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                expr = expr + s * branch_mult_prev.clone() * r_table[ind].clone();
            }
            constraints.push((
                "branch acc non-empty",
                q_enable.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * rlp2.clone()
                    * (branch_acc_cur - branch_acc_prev - expr),
            ));
            constraints.push((
                "branch acc mult non-empty",
                q_enable
                    * (one.clone() - is_node_hashed.clone())
                    * rlp2
                    * (branch_mult_cur
                        - branch_mult_prev * r_table[R_TABLE_LEN - 1].clone() * r_table[0].clone()),
            ));

            // TODO: is_node_hashed, the length is not fixed for this case,
            // key_len_lookup, mult_diff_lookup need to be used

            constraints
        });

        config
    }

    pub fn construct(config: BranchRLCConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchRLCChip<F> {
    type Config = BranchRLCConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
