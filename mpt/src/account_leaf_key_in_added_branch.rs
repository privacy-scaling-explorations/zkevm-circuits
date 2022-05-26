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
    param::{IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, ACCOUNT_DRIFTED_LEAF_IND, BRANCH_ROWS_NUM, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_KEY_C_IND},
};

use crate::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
    KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET, R_TABLE_LEN,
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyInAddedBranchConfig {}

pub(crate) struct AccountLeafKeyInAddedBranchChip<F> {
    config: AccountLeafKeyInAddedBranchConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyInAddedBranchChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        not_first_level: Column<Advice>,
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
    ) -> AccountLeafKeyInAddedBranchConfig {
        let config = AccountLeafKeyInAddedBranchConfig {};

        let one = Expression::Constant(F::one());
        let c16 = Expression::Constant(F::from(16_u64));
        let c32 = Expression::Constant(F::from(32_u64));
        let c48 = Expression::Constant(F::from(48_u64));
        let rot_branch_init = -ACCOUNT_DRIFTED_LEAF_IND - BRANCH_ROWS_NUM;

        // NOTE: the nonce/balance & storage root / codehash values are not stored in
        // this row, it needs to be the same
        // as for the leaf before it drifted down to the new branch, thus, it is
        // retrieved from the row of a leaf before a drift - to check that the hash
        // of a drifted leaf is in the new branch.

        // Checking leaf RLC is ok - RLC is then taken and nonce/balance & storage root
        // / codehash values are added to RLC, finally lookup is used to check
        // the hash that corresponds to this RLC is in the parent branch at
        // drifted_pos position. This is not to be confused with key RLC checked
        // in another gate (the gate here checks the RLC of all leaf bytes,
        // while the gate below checks the key RLC accumulated in
        // branches/extensions + leaf key).

        meta.create_gate("account drifted leaf: leaf RLC after key", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_level = one.clone() -  meta.query_advice(
                not_first_level,
                Rotation::cur(),
            );

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            constraints.push((
                "account leaf key s_rlp1 = 248",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (s_rlp1.clone() - c248),
            ));

            let mut ind = 0;
            let mut expr =
                s_rlp1 + meta.query_advice(s_rlp2, Rotation::cur()) * r_table[ind].clone();
            ind += 1;

            expr = expr
                + compute_rlc(
                    meta,
                    s_advices.to_vec(),
                    ind,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            expr = expr + c_rlp1.clone() * r_table[R_TABLE_LEN - 1].clone() * r_table[1].clone();
            expr = expr + c_rlp2.clone() * r_table[R_TABLE_LEN - 1].clone() * r_table[2].clone();

            let acc = meta.query_advice(acc_s, Rotation::cur());

            constraints.push(("leaf key acc", q_enable.clone()
                * (is_branch_s_placeholder + is_branch_c_placeholder) // drifted leaf appears only when there is a placeholder branch
                * (one.clone() - is_leaf_in_first_level.clone())
                * (expr - acc)));

            constraints
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_level = one.clone() -  meta.query_advice(
                not_first_level,
                Rotation::cur(),
            );

            q_enable * (is_branch_s_placeholder + is_branch_c_placeholder) * (one.clone() - is_leaf_in_first_level.clone())
        };

        /*
        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                q_enable,
                ind,
                s_advices[0],
                s_advices[ind],
                fixed_table,
            )
        }
        key_len_lookup(meta, sel, 32, s_advices[0], c_rlp1, fixed_table);
        key_len_lookup(meta, sel, 33, s_advices[0], c_rlp2, fixed_table);
        */

        // acc_mult corresponds to key length:
        mult_diff_lookup(meta, sel, 3, s_advices[0], acc_mult_s, fixed_table);

        /*
        Leaf key S
        Leaf key C
        Nonce balance S
        Nonce balance C
        Storage codehash S
        Storage codehash C
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

        meta.create_gate("Account drifted leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // Get back into S or C extension row to retrieve key_rlc. Note that this works
            // for both - extension nodes and branches. That's because branch key RLC is
            // stored in extension node row when there is NO extension node (the
            // constraint is in extension_node_key).
            let key_rlc_cur = meta.query_advice(key_rlc, Rotation(-ACCOUNT_DRIFTED_LEAF_IND-1));

            // sel1 and sel2 determines whether drifted_pos needs to be
            // multiplied by 16 or not.
            let sel1 = meta.query_advice(
                s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                // ok: -1, -4
                // not ok: -6, -7, -8
                // Rotation(-6),
                Rotation(rot_branch_init),
            );
            let sel2 = meta.query_advice(
                s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_branch_init),
            );

            // Note: previous key_rlc in sel1/sel2 could be queried instead.
            let branch_rlc_mult = meta.query_advice(key_rlc_mult, Rotation(-30));

            let mult_diff = meta.query_advice(mult_diff, Rotation(rot_branch_init + 1));

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

            let leaf_key_s_rlc = meta.query_advice(key_rlc, Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND)));
            let leaf_key_c_rlc = meta.query_advice(key_rlc, Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND)));

            let is_branch_in_first_level = one.clone() - meta.query_advice(
                not_first_level,
                Rotation(rot_branch_init),
            );

            let is_leaf_in_first_level = one.clone() -  meta.query_advice(
                not_first_level,
                Rotation::cur(),
            );

            let is_one_nibble = get_is_extension_node_one_nibble(meta, s_advices, rot_branch_init);

            // Any rotation that lands into branch children can be used.
            let drifted_pos = meta.query_advice(drifted_pos, Rotation(-17));
            let mut key_mult = branch_rlc_mult.clone()
                * mult_diff.clone()
                * (one.clone() - is_branch_in_first_level.clone())
                + is_branch_in_first_level.clone() * is_one_nibble.clone()
                + is_branch_in_first_level.clone()
                    * mult_diff.clone()
                    * (one.clone() - is_one_nibble.clone());
            let drifted_pos_mult =
                key_mult.clone() * c16.clone() * sel1.clone() + key_mult.clone() * sel2.clone();

            // Note: the difference in key_mult for sel1 and sel2 is already taken into
            // account in mult_diff.

            let key_rlc_start = key_rlc_cur.clone() + drifted_pos.clone() * drifted_pos_mult;

            // If sel1 = 1, we have one nibble+48 in s_advices[1].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());

            // If sel2 = 1, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_advice1.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
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
                "Drifted leaf key placeholder S",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (leaf_key_s_rlc.clone() - key_rlc_long.clone()),
            ));
            constraints.push((
                "Drifted leaf key placeholder C",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (leaf_key_c_rlc.clone() - key_rlc_long.clone()),
            ));

            constraints.push((
                "foo",
                q_enable.clone()
                    * sel1.clone()
                    * (one.clone() - one.clone())
            ));

            constraints
        });

        config
    }

    pub fn construct(config: AccountLeafKeyInAddedBranchConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafKeyInAddedBranchChip<F> {
    type Config = AccountLeafKeyInAddedBranchConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
