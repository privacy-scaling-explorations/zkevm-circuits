use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{
        compute_rlc, get_bool_constraint, get_is_extension_node_one_nibble, key_len_lookup,
        mult_diff_lookup, range_lookups,
    },
    mpt::FixedTableTag,
    param::{IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, LEAF_DRIFTED_IND, BRANCH_ROWS_NUM, LEAF_KEY_S_IND, LEAF_KEY_C_IND},
};

use crate::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
    KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET, R_TABLE_LEN,
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
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        mult_diff: Column<Advice>,
        drifted_pos: Column<Advice>,
        is_account_leaf_in_added_branch: Column<Advice>,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> LeafKeyInAddedBranchConfig {
        let config = LeafKeyInAddedBranchConfig {};

        let one = Expression::Constant(F::one());
        let c16 = Expression::Constant(F::from(16_u64));
        let c32 = Expression::Constant(F::from(32_u64));
        let c48 = Expression::Constant(F::from(48_u64));
        let rot_branch_init = -LEAF_DRIFTED_IND - BRANCH_ROWS_NUM;
        let rot_into_account = -LEAF_DRIFTED_IND - 1;

        // NOTE: the leaf value is not stored in this row, it needs to be the same
        // as for the leaf before it drifted down to the new branch, thus, it is
        // retrieved from the row of a leaf before a drift - to check that the hash
        // of a drifted leaf is in the new branch.

        // Checking leaf RLC is ok - RLC is then taken and value (from leaf_value row)
        // is added to RLC, finally lookup is used to check the hash that
        // corresponds to this RLC is in the parent branch at drifted_pos position.
        // This is not to be confused with key RLC checked in another gate (the gate
        // here checks the RLC of all leaf bytes, while the gate below checks the key
        // RLC accumulated in branches/extensions + leaf key).
        meta.create_gate("Storage leaf in added branch RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "is_long",
                q_enable.clone() * is_long.clone() * (s_rlp1.clone() - c248),
            ));
            constraints.push((
                "is_long is boolean",
                get_bool_constraint(q_enable.clone(), is_long.clone()),
            ));
            constraints.push((
                "is_short is boolean",
                get_bool_constraint(q_enable.clone(), is_long.clone()),
            ));
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            constraints.push((
                "is_long + is_short = 1 when leaf drifts",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (is_long.clone() + is_short.clone() - one.clone()),
            ));

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let mut rlc = s_rlp1 + s_rlp2 * r_table[0].clone();

            rlc = rlc + compute_rlc(meta, s_advices.to_vec(), 1, one.clone(), 0, r_table.clone());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            rlc = rlc + c_rlp1 * r_table[R_TABLE_LEN - 1].clone() * r_table[1].clone();
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            rlc = rlc + c_rlp2 * r_table[R_TABLE_LEN - 1].clone() * r_table[2].clone();

            let acc = meta.query_advice(acc_s, Rotation::cur());
            constraints.push(("Leaf key acc", q_enable
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (rlc - acc)));

            constraints
        });

        let sel_short = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());

            q_enable * is_short * (is_branch_s_placeholder + is_branch_c_placeholder)
                * (one.clone() - is_leaf_in_first_storage_level.clone())
        };
        let sel_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));
            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());

            q_enable * is_long * (is_branch_s_placeholder + is_branch_c_placeholder)
                * (one.clone() - is_leaf_in_first_storage_level.clone())
        };

        /*
        // There are 0s after key length.
        for ind in 0..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel_short,
                ind + 1,
                s_rlp2,
                s_advices[ind],
                fixed_table,
            )
        }

        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel_long,
                ind,
                s_advices[0],
                s_advices[ind],
                fixed_table,
            )
        }
        key_len_lookup(meta, sel_long, 32, s_advices[0], c_rlp1, fixed_table);
        */

        // acc_mult corresponds to key length (short):
        mult_diff_lookup(meta, sel_short, 2, s_rlp2, acc_mult_s, fixed_table);
        // acc_mult corresponds to key length (long):
        mult_diff_lookup(meta, sel_long, 3, s_advices[0], acc_mult_s, fixed_table);

        /*
        Leaf key S
        Leaf value S
        Leaf key C
        Leaf value C
        Drifted leaf (leaf in added branch)

        Add case (S branch is placeholder):
          Branch S           || Branch C             
          Placeholder branch || Added branch
          Leaf S             || Leaf C
                             || Drifted leaf (this is Leaf S drifted into Added branch)

          Leaf S needs to have the same RLC as Drifted leaf.
          Note that Leaf S RLC is computed by taking key_rlc from Branch S and then adding the bytes in Leaf key S row.
          Drifted leaf RLC is computed by taking key_rlc from Added branch and then adding the bytes in Drifted leaf row.

        Delete case (C branch is placeholder):
          Branch S                        || Branch C             
          Branch to be deleted            || Placeholder branch
          Leaf S (leaf to be deleted)     || Leaf C
          Leaf to be drifted one level up || 
        */

        meta.create_gate("Drifted leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // Get back into S or C extension row to retrieve key_rlc. Note that this works
            // for both - extension nodes and branches. That's because branch key RLC is
            // stored in extension node row when there is NO extension node (the
            // constraint is in extension_node_key).
            let key_rlc_cur = meta.query_advice(key_rlc, Rotation(-LEAF_DRIFTED_IND-1));

            // sel1 and sel2 determines whether drifted_pos needs to be
            // multiplied by 16 or not.
            let sel1 = meta.query_advice(
                s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let sel2 = meta.query_advice(
                s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );

            // Note: previous key_rlc in sel1/sel2 could be queried instead.
            let branch_rlc_mult = meta.query_advice(key_rlc_mult, Rotation(-30));

            let mult_diff = meta.query_advice(mult_diff, Rotation(rot_branch_init + 1));

            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());

            // Key RLC of the drifted leaf needs to be the same as key RLC of the leaf
            // before it drifted down into extension/branch.
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );

            let leaf_key_s_rlc = meta.query_advice(key_rlc, Rotation(-(LEAF_DRIFTED_IND - LEAF_KEY_S_IND)));
            let leaf_key_c_rlc = meta.query_advice(key_rlc, Rotation(-(LEAF_DRIFTED_IND - LEAF_KEY_C_IND)));

            // whether placeholder branch is in the first storage level:
            let is_branch_in_first_storage_level = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_branch_init - 1),
            );

            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            let is_one_nibble = get_is_extension_node_one_nibble(meta, s_advices, rot_branch_init);

            // Any rotation that lands into branch children can be used.
            let drifted_pos = meta.query_advice(drifted_pos, Rotation(-17));
            let mut key_mult = branch_rlc_mult.clone()
                * mult_diff.clone()
                * (one.clone() - is_branch_in_first_storage_level.clone())
                + is_branch_in_first_storage_level.clone() * is_one_nibble.clone()
                + is_branch_in_first_storage_level.clone()
                    * mult_diff.clone()
                    * (one.clone() - is_one_nibble.clone());
            let drifted_pos_mult =
                key_mult.clone() * c16.clone() * sel1.clone() + key_mult.clone() * sel2.clone();

            // Note: the difference in key_mult for sel1 and sel2 is already taken into
            // account in mult_diff.

            let key_rlc_start = key_rlc_cur.clone() + drifted_pos.clone() * drifted_pos_mult;

            // If sel1 = 1, we have one nibble+48 in s_advices[0].
            let s_advice0 = meta.query_advice(s_advices[0], Rotation::cur());

            // If sel2 = 1, we have 32 in s_advices[0].
            constraints.push((
                "Leaf key acc s_advice0",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_advice0.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * is_short.clone(),
            ));

            let mut key_rlc_short = key_rlc_start.clone()
                + (s_advice0.clone() - c48.clone()) * sel1.clone() * key_mult.clone();

            for ind in 1..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_short = key_rlc_short + s * key_mult.clone() * r_table[ind - 1].clone();
            }

            // Note: drifted leaf key can't reach c_rlp1 because it has at most 31 nibbles.
            // In case of 31 nibbles, key occupies 32 bytes (in case of 32 nibbles and no
            // branch above the leaf, the key occupies 33 bytes).

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc.
            constraints.push((
                "Drifted leaf key placeholder S",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * is_short.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_s_rlc.clone() - key_rlc_short.clone()),
            ));
            constraints.push((
                "Drifted leaf key placeholder C",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * is_short.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_c_rlc.clone() - key_rlc_short.clone()),
            ));

            // Long:
            // Note: long means long leaf RLP, not extension node nibbles.

            // If sel1 = 1, we have one nibble+48 in s_advices[1].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());

            // If sel2 = 1, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (s_advice1.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * is_long.clone(),
            ));

            let mut key_rlc_long = key_rlc_start.clone()
                + (s_advice1.clone() - c48.clone()) * sel1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_mult = key_mult * r_table[0].clone();
                key_rlc_long = key_rlc_long + s * key_mult.clone();
            }

            key_mult = key_mult * r_table[0].clone();
            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            key_rlc_long = key_rlc_long + c_rlp1.clone() * key_mult;

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc.
            constraints.push((
                "Drifted leaf key placeholder S long",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * is_long.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_s_rlc.clone() - key_rlc_long.clone()),
            ));
            constraints.push((
                "Drifted leaf key placeholder C long",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * is_long.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_c_rlc.clone() - key_rlc_long.clone()),
            ));

            constraints
        });

        // Checking accumulated RLC for key is not necessary here for
        // leaf_key_in_added_branch because we check this for leaf_key and here
        // we only check the key in leaf_key_in_added_branch corresponds to the
        // one in leaf_key.

        // If the branch is placeholder, we need to check that the leaf without the
        // first nibble has a hash which is in the branch at drifted_pos
        // position.

        // In case we have a placeholder branch at position S:
        // (1) branch (17 rows) which contains leaf that turns into branch at
        // is_modified position (S positions) |     branch (17 rows) that
        // contains added branch hash at is_modified position (C positions)
        // (2) placeholder branch (17 rows) (S positions) | added branch (17 rows) (C
        // positions)     S extension node row
        //     C extension node row
        // (3) leaf key S
        // (4) leaf value S ((3)||(4) hash is two levels above in (1) at is_modified)
        // (5) leaf key C
        // (6) leaf value C ((5)||(6) hash is in one level above (2) at is_modified)
        // (7) leaf in added branch - the same as leaf key S in (3), but it has the
        // first nibble removed

        // We need to check that leaf_in_added_branch hash is in (2) at drifted_pos
        // position (drifted_pos is the first nibble in leaf key S (3), because
        // leaf drifts down to this position in new branch)

        // We need to construct RLP of the leaf. We have leaf key in
        // is_leaf_in_added_branch and the value is the same as it is in the
        // leaf value S (3).

        meta.lookup_any("leaf_key_in_added_branch 1", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let mut rlc = meta.query_advice(acc_s, Rotation::cur());
            let acc_mult = meta.query_advice(acc_mult_s, Rotation::cur());

            // If branch placeholder in S, value is 3 above.
            let rot_val = -3;

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation(rot_val));
            rlc = rlc + s_rlp1 * acc_mult.clone();

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation(rot_val));
            rlc = rlc + s_rlp2 * acc_mult.clone() * r_table[0].clone();

            rlc = rlc
                + compute_rlc(
                    meta,
                    s_advices.to_vec(),
                    1,
                    acc_mult.clone(),
                    rot_val,
                    r_table.clone(),
                );
            // Note: value doesn't reach c_rlp1.

            // If leaf without branch, then there is no added branch.
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            // Any rotation that lands into branch children can be used.
            let rot = -17;
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-23),
            );

            constraints.push((
                q_enable.clone()
                    * rlc
                    * is_branch_s_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch.clone()),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            // placeholder branch contains hash of a leaf that moved to added branch
            let s_mod_node_hash_rlc = meta.query_advice(s_mod_node_hash_rlc, Rotation(rot));
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * s_mod_node_hash_rlc
                    * is_branch_s_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch),
                keccak_table_i,
            ));

            constraints
        });

        meta.lookup_any("leaf_key_in_added_branch 2", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let mut rlc = meta.query_advice(acc_s, Rotation::cur());
            let acc_mult = meta.query_advice(acc_mult_s, Rotation::cur());

            // If branch placeholder in C, value is 1 above.
            let rot_val = -1;

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation(rot_val));
            rlc = rlc + s_rlp1 * acc_mult.clone();

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation(rot_val));
            rlc = rlc + s_rlp2 * acc_mult.clone() * r_table[0].clone();

            rlc = rlc
                + compute_rlc(
                    meta,
                    s_advices.to_vec(),
                    1,
                    acc_mult.clone(),
                    rot_val,
                    r_table.clone(),
                );
            // Note: value doesn't reach c_rlp1.

            // If leaf without branch, then there is no added branch.
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            // Any rotation that lands into branch children can be used.
            let rot = -17;
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-23),
            );

            constraints.push((
                q_enable.clone()
                    * rlc
                    * is_branch_c_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch.clone()),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            // placeholder branch contains hash of a leaf that moved to added branch
            let c_mod_node_hash_rlc = meta.query_advice(c_mod_node_hash_rlc, Rotation(rot));
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * c_mod_node_hash_rlc
                    * is_branch_c_placeholder.clone()
                    * (one - is_leaf_without_branch),
                keccak_table_i,
            ));

            constraints
        });

        range_lookups(
            meta,
            q_enable,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_rlp1, s_rlp2, c_rlp1, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

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
