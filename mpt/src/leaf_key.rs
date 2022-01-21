use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{HASH_WIDTH, R_TABLE_LEN};

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyConfig {}

// Verifies the RLC of leaf RLP: RLP meta data & key (value and then hash of
// the whole RLC are checked in leaf_value).
// Verifies RLC of a leaf key - used for a check from outside the circuit to verify
// that the proper key is used.
pub(crate) struct LeafKeyChip<F> {
    config: LeafKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        s_keccak0: Column<Advice>, // to see whether it's long or short RLP
        s_keccak1: Column<Advice>, // to see whether it's long or short RLP
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        is_branch_placeholder: Column<Advice>,
        modified_node: Column<Advice>,
        r_table: Vec<Expression<F>>,
        is_s: bool,
    ) -> LeafKeyConfig {
        let config = LeafKeyConfig {};

        // TODO: if key is of length 1, then there is one less byte in RLP meta data
        // (this is easier seen in extension nodes, it will probably be difficult
        // to generate such test for normal ShortNode)

        // Checking leaf RLC is ok - this value is then taken in the next row, where
        // leaf value is added to RLC, finally lookup is used to check the hash that
        // corresponds to this RLC is in the parent branch.
        meta.create_gate("Storage leaf RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let is_long = meta.query_advice(s_keccak0, Rotation::cur());
            let is_short = meta.query_advice(s_keccak1, Rotation::cur());
            constraints.push((
                "is long",
                q_enable.clone() * is_long * (s_rlp1.clone() - c248),
            ));

            // TODO: is_long, is_short are booleans
            // TODO: is_long + is_short = 1

            // TODO: check that from some point on (depends on the rlp meta data)
            // the values are zero (as in key_compr) - but take into account it can be long or short RLP

            // TODO: check acc_mult as in leaf_key_in_added_branch

            let mut rlc = s_rlp1;
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * r_table[0].clone();

            let mut rind = 1;
            let mut r_wrapped = false;
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                if !r_wrapped {
                    rlc = rlc + s * r_table[rind].clone();
                } else {
                    rlc = rlc
                        + s * r_table[rind].clone()
                            * r_table[R_TABLE_LEN - 1].clone();
                }
                if rind == R_TABLE_LEN - 1 {
                    rind = 0;
                    r_wrapped = true;
                } else {
                    rind += 1;
                }
            }

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            rlc = rlc
                + c_rlp1
                    * r_table[R_TABLE_LEN - 1].clone()
                    * r_table[1].clone();

            // key is at most of length 32, so it doesn't go further than c_rlp1

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("Leaf key acc", q_enable * (rlc - acc)));

            constraints
        });

        // Checking the key - accumulated RLC is taken (computed using the path through branches)
        // and key bytes are added to the RLC. The external circuit can check
        // the key (where value in trie is being set at key) RLC is the same as in key_rlc column.
        meta.create_gate("Storage leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_long = meta.query_advice(s_keccak0, Rotation::cur());
            let is_short = meta.query_advice(s_keccak1, Rotation::cur());

            // key rlc is in the first branch node (not branch init)
            let mut rot = -18;
            if !is_s {
                rot = -20;
            }

            let key_rlc_acc_start = meta.query_advice(key_rlc, Rotation(rot));
            let key_mult_start = meta.query_advice(key_rlc_mult, Rotation(rot));
            // sel1 and sel2 are in init branch
            let sel1 = meta.query_advice(sel1, Rotation(rot - 1));
            let sel2 = meta.query_advice(sel2, Rotation(rot - 1));

            let one = Expression::Constant(F::one());
            let c16 = Expression::Constant(F::from(16));
            let c32 = Expression::Constant(F::from(32));
            let c48 = Expression::Constant(F::from(48));

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot - 1));

            // If the last branch is placeholder (the placeholder branch is the same as its
            // parallel counterpart), there is a branch modified_index nibble already
            // incorporated in key_rlc. That means we need to ignore the first nibble here (in leaf key).

            // For short RLP (key starts at s_advices[0]):

            // If sel1 = 1, we have one nibble+48 in s_advices[0].
            let s_advice0 = meta.query_advice(s_advices[0], Rotation::cur());
            let mut key_rlc_acc_short = key_rlc_acc_start.clone()
                + (s_advice0.clone() - c48.clone())
                    * key_mult_start.clone()
                    * sel1.clone();
            let mut key_mult =
                key_mult_start.clone() * r_table[0].clone() * sel1.clone();
            key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1 and !is_branch_placeholder, we have 32 in s_advices[0].
            constraints.push((
                "Leaf key acc s_advice0",
                q_enable.clone()
                    * (s_advice0.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_branch_placeholder.clone())
                    * is_short.clone(),
            ));

            let s_advices1 = meta.query_advice(s_advices[1], Rotation::cur());
            key_rlc_acc_short =
                key_rlc_acc_short + s_advices1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_short = key_rlc_acc_short
                    + s * key_mult.clone() * r_table[ind - 2].clone();
            }

            let key_rlc = meta.query_advice(key_rlc, Rotation::cur());

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_short.
            constraints.push((
                "Key RLC short",
                q_enable.clone()
                    * (key_rlc_acc_short - key_rlc.clone())
                    * (one.clone() - is_branch_placeholder.clone())
                    * is_short.clone(),
            ));

            // For long RLP (key starts at s_advices[1]):

            // If sel1 = 1, we have nibble+48 in s_advices[1].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
            let mut key_rlc_acc_long = key_rlc_acc_start.clone()
                + (s_advice1.clone() - c48)
                    * key_mult_start.clone()
                    * sel1.clone();
            let mut key_mult =
                key_mult_start.clone() * r_table[0].clone() * sel1.clone();
            key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1 and !is_branch_placeholder, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (s_advice1.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_branch_placeholder.clone())
                    * is_long.clone(),
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + s_advices2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_long = key_rlc_acc_long
                    + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            let c_rlp1_cur = meta.query_advice(c_rlp1, Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long
                + c_rlp1_cur.clone() * key_mult * r_table[29].clone();

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_long.
            constraints.push((
                "Key RLC long",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc.clone())
                    * (one.clone() - is_branch_placeholder.clone())
                    * is_long.clone(),
            ));

            // For leaf under placeholder branch we don't need to check key RLC -
            // this leaf is something we didn't ask for. For example, when setting a leaf L
            // causes that leaf L1 (this is the leaf under branch placeholder)
            // is replaced by branch, then we get placeholder branch at S positions
            // and leaf L1 under it. However, key RLC needs to be compared for leaf L,
            // because this is where the key was changed (but it causes to change also L1).
            // In delete, the situation is just turned around.

            // However, note that hash of leaf L1 needs to be checked to be in the branch
            // above the placeholder branch - this is checked in leaf_value (where RLC
            // from the first gate above is used).

            // Also, it needs to be checked that leaf L1 is the same as the leaf that
            // is in the branch parallel to the placeholder branch
            // (at position is_at_first_nibble) - same with the exception of one nibble.
            // This is checked in leaf_key_in_added_branch.

            constraints
        });

        config
    }

    pub fn construct(config: LeafKeyConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for LeafKeyChip<F> {
    type Config = LeafKeyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
