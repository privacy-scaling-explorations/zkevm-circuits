use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pairing::{arithmetic::FieldExt, bn256::Fr as Fp};
use std::marker::PhantomData;

use crate::param::{HASH_WIDTH, R_TABLE_LEN};

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyConfig {}

// Verifies RLC of a leaf key.
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

        meta.create_gate("Storage leaf key hash RLC", |meta| {
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

            // TODO: check acc_mult as in key_compr

            let mut hash_rlc = s_rlp1;
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            hash_rlc = hash_rlc + s_rlp2 * r_table[0].clone();
            let mut rind = 1;

            let mut r_wrapped = false;
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                if !r_wrapped {
                    hash_rlc = hash_rlc + s * r_table[rind].clone();
                } else {
                    hash_rlc = hash_rlc
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
            hash_rlc = hash_rlc
                + c_rlp1
                    * r_table[R_TABLE_LEN - 1].clone()
                    * r_table[1].clone();

            // key is at most of length 32, so it doesn't go further than c_rlp1

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("Leaf key acc", q_enable * (hash_rlc - acc)));

            constraints
        });

        meta.create_gate("Storage leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_long = meta.query_advice(s_keccak0, Rotation::cur());
            let is_short = meta.query_advice(s_keccak1, Rotation::cur());

            // key rlc is in the first branch node
            let mut rot = -16;
            if !is_s {
                rot = -18;
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

            // Key RLC is be checked to verify that the proper key is used.
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

            // Key RLC is be checked to verify that the proper key is used.
            constraints.push((
                "Key RLC long is_placeholder",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc.clone())
                    * is_long.clone(),
            ));

            // branch_is_placeholder section:

            // For short RLP and is_branch_placeholder (key starts at s_advices[0]):
            // If the last branch is placeholder, sel1 and sel2 are turned around.

            // If sel2 = 1, we have one nibble+48 in s_advices[0]. This is the nibble we ignore
            // because of "is_branch_placeholder".

            key_rlc_acc_short = key_rlc_acc_start.clone();
            key_mult = key_mult_start.clone();

            // If sel1 = 1 and is_branch_placeholder, we have 32 in s_advices[0].
            constraints.push((
                "Leaf key acc s_advice0 is_placeholder",
                q_enable.clone()
                    * (s_advice0 - c32.clone())
                    * sel1.clone()
                    * is_branch_placeholder.clone()
                    * is_short.clone(),
            ));

            // If sel1 = 1, s_advices[1] contains two nibbles, the first nibble
            // (which is modified_node) needs to be ignored.
            // modified_node is the same for all branch rows, -4 brings us into branch rows
            // for both, S and C key (-3 would work too, but rotation -4 is used in leaf_value)
            let modified_node = meta.query_advice(modified_node, Rotation(-4));

            // TODO: prepare test for sel1 = 1

            key_rlc_acc_short = key_rlc_acc_short
                + (s_advice1.clone() - modified_node.clone() * c16.clone())
                    * sel1.clone()
                    * key_mult.clone()
                + s_advice1.clone() * sel2.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_short = key_rlc_acc_short
                    + s * key_mult.clone() * r_table[ind - 2].clone();
            }

            // Key RLC is be checked to verify that the proper key is used.
            constraints.push((
                "Key RLC short is_placeholder",
                q_enable.clone()
                    * (key_rlc_acc_short - key_rlc.clone())
                    * is_branch_placeholder.clone()
                    * is_short,
            ));

            // For long RLP and is_branch_placeholder (key starts at s_advices[1]):
            // If the last branch is placeholder, sel1 and sel2 are turned around.

            // If sel2 = 1, we have one nibble+48 in s_advices[1]. This is the nibble we ignore
            // because of "is_branch_placeholder".
            let mut key_rlc_acc_long = key_rlc_acc_start.clone();
            key_mult = key_mult_start.clone();

            // If sel1 = 1 and is_branch_placeholder, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1 is_placeholder",
                q_enable.clone()
                    * (s_advice1 - c32.clone())
                    * sel1.clone()
                    * is_branch_placeholder.clone()
                    * is_long.clone(),
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());

            // If sel1 = 1, s_advices[2] contains two nibbles, the first nibble
            // (which is modified_node) needs to be ignored.
            // modified_node is the same for all branch rows, -4 brings us into branch rows
            // for both, S and C key (-3 would work too, but rotation -4 is used in leaf_value)

            key_rlc_acc_long = key_rlc_acc_long
                + (s_advices2.clone() - modified_node.clone() * c16.clone())
                    * sel1.clone()
                    * key_mult.clone()
                + s_advices2.clone() * sel2.clone() * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_long = key_rlc_acc_long
                    + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            // TODO: prepare a test for this

            key_rlc_acc_long =
                key_rlc_acc_long + c_rlp1_cur * key_mult * r_table[29].clone();

            // Key RLC is be checked to verify that the proper key is used.
            constraints.push((
                "Key RLC long is_placeholder",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc.clone())
                    * is_branch_placeholder.clone()
                    * is_long,
            ));

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
