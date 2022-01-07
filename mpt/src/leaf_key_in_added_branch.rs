use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS,
    KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET, R_TABLE_LEN,
};

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyInAddedBranchConfig {}

pub(crate) struct LeafKeyInAddedBranchChip<F> {
    config: LeafKeyInAddedBranchConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyInAddedBranchChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        s_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH], // to check hash && to see whether it's long or short RLP
        c_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH], // to check hash && to see whether it's long or short RLP
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        modified_node: Column<Advice>,
        r_table: Vec<Expression<F>>,
        r_mult_table: [Column<Fixed>; 2],
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> LeafKeyInAddedBranchConfig {
        let config = LeafKeyInAddedBranchConfig {};

        // TODO: leaf and leaf in added branch differs in first_nibble

        // Checking leaf RLC is ok - this value is then taken and value is added
        // to RLC, finally lookup is used to check the hash that
        // corresponds to this RLC is in the parent branch at first_nibble position.
        meta.create_gate("Storage leaf in added branch RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // TODO: is_long, is_short are booleans
            // TODO: is_long + is_short = 1

            // TODO: check there is 248 in long

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());

            // TODO: check that from some point on (depends on the rlp meta data)
            // the values are zero (as in key_compr) - but take into account it can be long or short RLP

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

        // Check acc_mult when RLP metadata is two bytes (short)
        meta.lookup_any(|meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let two = Expression::Constant(F::from(2_u64));

            let is_short = meta.query_advice(s_keccak[1], Rotation::cur());

            let c128 = Expression::Constant(F::from(128));
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let key_len = s_rlp2 - c128;
            let acc_mult = meta.query_advice(acc_mult, Rotation::cur());

            constraints.push((
                q_enable.clone() * (key_len + two) * is_short.clone(), // when short, there are 2 RLP meta data
                meta.query_fixed(r_mult_table[0], Rotation::cur()),
            ));
            constraints.push((
                q_enable.clone() * acc_mult * is_short,
                meta.query_fixed(r_mult_table[1], Rotation::cur()),
            ));

            constraints
        });

        // Check acc_mult when RLP metadata is three bytes (long)
        meta.lookup_any(|meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let three = Expression::Constant(F::from(3_u64));

            let is_long = meta.query_advice(s_keccak[0], Rotation::cur());

            let c128 = Expression::Constant(F::from(128));
            let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());
            let key_len = s_advices0 - c128;
            let acc_mult = meta.query_advice(acc_mult, Rotation::cur());

            constraints.push((
                q_enable.clone() * (key_len + three) * is_long.clone(), // when long, there are 3 RLP meta data
                meta.query_fixed(r_mult_table[0], Rotation::cur()),
            ));
            constraints.push((
                q_enable.clone() * acc_mult * is_long,
                meta.query_fixed(r_mult_table[1], Rotation::cur()),
            ));

            constraints
        });

        // Checking accumulated RLC for key is not necessary here for leaf_key_in_added_branch
        // because we check this for leaf_key and here we only check the key in leaf_key_in_added_branch
        // corresponds to the one in leaf_key.

        // If the branch is placeholder, we need to check that the leaf without the first
        // nibble has a hash which is in the branch at first_nibble position.

        // In case we have a placeholder branch at position S:
        // (1) branch which contains leaf that turns into branch at is_modified position (S positions) | branch that contains added branch hash at is_modified position (C positions)
        // (2) placeholder branch (S positions) | added branch (C positions)
        // S and C extension node rows
        // (3) leaf key S
        // (4) leaf value S ((3)||(4) hash is two levels above in (1) at is_modified)
        // (5) leaf key C
        // (6) leaf value C ((5)||(6) hash is in one level above (2) at is_modified)
        // (7) leaf in added branch - the same as leaf key S in (3), but it has the first nibble removed

        // We need to check that leaf_in_added_branch hash is in (2) at first_nibble position
        // (first_nibble is the first nibble in leaf key S (3), because leaf drifts down to
        // this position in new branch)

        // We need to construct RLP of the leaf. We have leaf key in is_leaf_in_added_branch
        // and the value is the same as it is in the leaf value S (3).

        meta.lookup_any(|meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let mut rlc = meta.query_advice(acc, Rotation::cur());
            let acc_mult = meta.query_advice(acc_mult, Rotation::cur());

            // If branch placeholder in S, value is 3 above.
            let rot_val = -3;

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation(rot_val));
            rlc = rlc + s_rlp1 * acc_mult.clone();

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation(rot_val));
            rlc = rlc + s_rlp2 * acc_mult.clone() * r_table[0].clone();

            let mut rind = 1;
            let mut r_wrapped = false;
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation(rot_val));
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

            // Any rotation that lands into branch children can be used.
            let rot = -17;
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-23),
            );

            constraints.push((
                q_enable.clone() * rlc * is_branch_s_placeholder.clone(),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            for (ind, column) in s_keccak.iter().enumerate() {
                // placeholder branch contains hash of a leaf that moved to added branch
                let s_keccak = meta.query_advice(*column, Rotation(rot));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    q_enable.clone()
                        * s_keccak
                        * is_branch_s_placeholder.clone(),
                    keccak_table_i,
                ));
            }

            constraints
        });

        meta.lookup_any(|meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let mut rlc = meta.query_advice(acc, Rotation::cur());
            let acc_mult = meta.query_advice(acc_mult, Rotation::cur());

            // If branch placeholder in C, value is 1 above.
            let rot_val = -1;

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation(rot_val));
            rlc = rlc + s_rlp1 * acc_mult.clone();

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation(rot_val));
            rlc = rlc + s_rlp2 * acc_mult.clone() * r_table[0].clone();

            let mut rind = 1;
            let mut r_wrapped = false;
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation(rot_val));
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

            // Any rotation that lands into branch children can be used.
            let rot = -17;
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-23),
            );

            constraints.push((
                q_enable.clone() * rlc * is_branch_c_placeholder.clone(),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            for (ind, column) in c_keccak.iter().enumerate() {
                // placeholder branch contains hash of a leaf that moved to added branch
                let c_keccak = meta.query_advice(*column, Rotation(rot));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    q_enable.clone()
                        * c_keccak
                        * is_branch_c_placeholder.clone(),
                    keccak_table_i,
                ));
            }

            constraints
        });

        // TODO: "when placeholder" constraints - the branch that is parallel to the placeholder
        // branch needs to be checked to have exactly two non empty leaves: one is at is_modified
        // and one at is_at_first_nibble (is_modified is checked in leaf_key and leaf_value).
        // the leaf at first_nibble needs to be the same as the leaf at is_modified
        // in the previous branch (and at parallel position)
        /*
        meta.create_gate("branch placeholder", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_branch_init_cur =
                meta.query_advice(is_branch_init, Rotation::cur());

            let mut constraints = vec![];

            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-16),
            );

            constraints.push((
                "branch mult C row 0 (3)",
                q_enable
                    * is_branch_init_cur
                    * three_rlp_bytes_c
                    * (mult_c_three - branch_mult_c_cur),
            ));

            constraints
        });
        */

        config
    }

    pub fn construct(config: LeafKeyInAddedBranchConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for LeafKeyInAddedBranchChip<F> {
    type Config = LeafKeyInAddedBranchConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
