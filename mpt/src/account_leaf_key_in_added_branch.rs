use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation, circuit::Region,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{
        compute_rlc, get_is_extension_node_one_nibble, key_len_lookup,
        mult_diff_lookup, range_lookups,
    },
    mpt::{FixedTableTag, MainCols, AccumulatorCols, DenoteCols, MPTConfig, ProofVariables},
    param::{IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, ACCOUNT_DRIFTED_LEAF_IND, BRANCH_ROWS_NUM, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_NONCE_BALANCE_S_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND},
};

use crate::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
    KECCAK_OUTPUT_WIDTH, RLP_NUM, R_TABLE_LEN,
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyInAddedBranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyInAddedBranchConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        not_first_level: Column<Advice>,
        s_main: MainCols,
        c_main: MainCols,
        accs: AccumulatorCols, // accs.acc_c contains mult_diff_nonce, initially key_rlc was used for mult_diff_nonce, but it caused PoisonedConstraint in extension_node_key
        drifted_pos: Column<Advice>,
        denoter: DenoteCols,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> Self {
        let config = AccountLeafKeyInAddedBranchConfig { _marker: PhantomData };

        // Note: q_enable switches off the first level, there is no need for checks
        // for the first level because when the leaf appears in an added branch, it is at least
        // in the second level (added branch being above it).

        let one = Expression::Constant(F::one());
        let c16 = Expression::Constant(F::from(16_u64));
        let c32 = Expression::Constant(F::from(32_u64));
        let c48 = Expression::Constant(F::from(48_u64));
        let rot_branch_init = -ACCOUNT_DRIFTED_LEAF_IND - BRANCH_ROWS_NUM;
 
        meta.create_gate("Account drifted leaf: intermediate leaf RLC after key", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());

            /*
            `s_rlp1` is always 248 because the account leaf is always longer than 55 bytes.
            */
            constraints.push((
                "Account leaf key s_rlp1 = 248",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_rlp1.clone() - c248),
            ));

            let mut ind = 0;
            let mut expr =
                s_rlp1 + meta.query_advice(s_main.rlp2, Rotation::cur()) * r_table[ind].clone();
            ind += 1;

            expr = expr
                + compute_rlc(
                    meta,
                    s_main.bytes.to_vec(),
                    ind,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            expr = expr + c_rlp1.clone() * r_table[R_TABLE_LEN - 1].clone() * r_table[1].clone();
            expr = expr + c_rlp2.clone() * r_table[R_TABLE_LEN - 1].clone() * r_table[2].clone();

            let acc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            /*
            We check that the leaf RLC is properly computed. RLC is then taken and
            nonce/balance & storage root / codehash values are added to the RLC (note that nonce/balance
            & storage root / codehash are not stored for the drifted leaf because these values stay
            the same as in the leaf before drift).
            Finally, the lookup is used to check the hash that corresponds to this RLC is
            in the parent branch at `drifted_pos` position.
            This is not to be confused with the key RLC
            checked in another gate (the gate here checks the RLC of all leaf bytes,
            while the gate below checks the key RLC accumulated in
            branches/extensions and leaf key).
            */
            constraints.push(("Leaf key intermediate RLC", q_enable.clone()
                * (is_branch_s_placeholder + is_branch_c_placeholder) // drifted leaf appears only when there is a placeholder branch
                * (expr - acc)));

            constraints
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            q_enable * (is_branch_s_placeholder + is_branch_c_placeholder) 
        };

        /*
        /*
        Similarly as in account_leaf_key.rs,
        key RLC is computed over `s_main.bytes[1]`, ..., `s_main.bytes[31]` because we do not know
        the key length in advance. To prevent changing the key and setting `s_main.bytes[i]` for
        `i > nonce_len + 1` to get the desired nonce RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.
        The key can also appear in `c_main.rlp1` and `c_main.rlp2`, so we need to check these two columns too.
        */
        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                q_enable,
                ind,
                s_main.bytes[0],
                s_main.bytes[ind],
                128,
                fixed_table,
            )
        }
        key_len_lookup(meta, sel, 32, s_main.bytes[0], c_rlp1, 128, fixed_table);
        key_len_lookup(meta, sel, 33, s_main.bytes[0], c_rlp2, 128, fixed_table);
        */

        /*
        When the full account RLC is computed (see add_constraints below), we need to know
        the intermediate RLC and the randomness multiplier (`r` to some power) from the key row.
        The power of randomness `r` is determined by the key length - the intermediate RLC in the current row
        is computed as (key starts in `s_main.bytes[1]`):
        `rlc = s_main.rlp1 + s_main.rlp2 * r + s_main.bytes[0] * r^2 + key_bytes[0] * r^3 + ... + key_bytes[key_len-1] * r^{key_len + 2}`
        So the multiplier to be used in the next row is `r^{key_len + 2}`. 

        `mult_diff` needs to correspond to the key length + 2 RLP bytes + 1 byte for byte that contains the key length.
        That means `mult_diff` needs to be `r^{key_len+1}` where `key_len = s_main.bytes[0] - 128`.

        Note that the key length is different than the on of the leaf before it drifted (by one nibble
        if a branch is added, by multiple nibbles if extension node is added).
        */
        mult_diff_lookup(meta, sel, 3, s_main.bytes[0], accs.acc_s.mult, 128, fixed_table);

        /*
        Leaf key S
        Leaf key C
        Account non existing
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
            // Drifted leaf in added branch has the same key as it had it before it drifted down to the new branch.
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // Get back into S or C extension row to retrieve key_rlc. Note that this works
            // for both - extension nodes and branches. That's because branch key RLC is
            // stored in extension node row when there is NO extension node (the
            // constraint is in extension_node_key).
            let key_rlc_cur = meta.query_advice(accs.key.rlc, Rotation(-ACCOUNT_DRIFTED_LEAF_IND-1));
            // Note: key_rlc_cur means key RLC at added branch, we now need to add the bytes stored in drifted leaf key.

            // sel1 and sel2 determines whether drifted_pos needs to be
            // multiplied by 16 or not.
            let sel1 = meta.query_advice(
                s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let sel2 = meta.query_advice(
                s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            let is_branch_in_first_level = one.clone() - meta.query_advice(
                not_first_level,
                Rotation(rot_branch_init),
            );

            // Key RLC of the drifted leaf needs to be the same as key RLC of the leaf
            // before it drifted down into extension/branch.
            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            // Note: we could use rotation -30 to get branch_rlc_mult
            // (like meta.query_advice(key_rlc_mult, Rotation(-30))), but this throws an error
            // when account is in the first or second level. However, acc_mult_c in the account
            // leaf row stores this value too (the constraints for this are in account_leaf_key).
            let branch_rlc_mult = meta.query_advice(accs.acc_c.mult, Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND)));

            let mult_diff = meta.query_advice(accs.mult_diff, Rotation(rot_branch_init + 1)); 

            let leaf_key_s_rlc = meta.query_advice(accs.key.rlc, Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND)));
            let leaf_key_c_rlc = meta.query_advice(accs.key.rlc, Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND)));

            let is_one_nibble = get_is_extension_node_one_nibble(meta, s_main.bytes, rot_branch_init);

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

            // If sel1 = 1, we have one nibble+48 in s_main.bytes[1].
            let s_advice1 = meta.query_advice(s_main.bytes[1], Rotation::cur());

            // If sel2 = 1, we have 32 in s_main.bytes[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_advice1.clone() - c32.clone())
                    * sel2.clone()
            ));

            let mut key_rlc = key_rlc_start.clone()
                + (s_advice1.clone() - c48.clone()) * sel1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_mult = key_mult * r_table[0].clone();
                key_rlc = key_rlc + s * key_mult.clone();
            }

            key_mult = key_mult * r_table[0].clone();
            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            key_rlc = key_rlc + c_rlp1.clone() * key_mult.clone();

            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            key_rlc = key_rlc + c_rlp2.clone() * key_mult * r_table[0].clone();

            /*
            Note: no need to distinguish between sel1 and sel2 here as it was already
            when computing key_rlc.
            */

            /*
            The key RLC of the drifted leaf needs to be the same as the key RLC of the leaf before
            the drift - the nibbles are the same in both cases, the difference is that before the
            drift some nibbles are stored in the leaf key, while after the drift these nibbles are used as 
            position in a branch or/and nibbles of the extension node.
            */
            constraints.push((
                "Drifted leaf key RLC same as the RLC of the leaf before drift (placeholder S)",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * (leaf_key_s_rlc.clone() - key_rlc.clone()),
            ));
            constraints.push((
                "Drifted leaf key RLC same as the RLC of the leaf before drift (placeholder C)",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * (leaf_key_c_rlc.clone() - key_rlc.clone()),
            ));

            constraints
        });

        let add_constraints =
            |meta: &mut VirtualCells<F>,
            constraints: &mut Vec<(Expression<F>, Expression<F>)>,
            is_s: bool | {

            let q_enable = q_enable(meta);
            let mut rlc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
            let acc_mult = meta.query_advice(accs.acc_s.mult, Rotation::cur());

            /*
            Leaf key S
            Leaf key C
            Nonce balance S
            Nonce balance C
            Storage codehash S
            Storage codehash C
            Drifted leaf (leaf in added branch)
            */

            let mut nonce_rot = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND);
            if !is_s {
                nonce_rot = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_NONCE_BALANCE_C_IND);
            }
            let mut storage_codehash_rot = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND);
            if !is_s {
                storage_codehash_rot = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND);
            }

            let mult_diff_nonce = meta.query_advice(accs.acc_c.rlc, Rotation(nonce_rot));

            let s_rlp1_nonce = meta.query_advice(s_main.rlp1, Rotation(nonce_rot));
            rlc = rlc + s_rlp1_nonce * acc_mult.clone();

            let s_rlp2_nonce = meta.query_advice(s_main.rlp2, Rotation(nonce_rot));
            let mut rind = 0;
        
            rlc = rlc + s_rlp2_nonce * acc_mult.clone() * r_table[rind].clone();
            rind += 1;

            let c_rlp1_nonce = meta.query_advice(c_main.rlp1, Rotation(nonce_rot));
            let c_rlp2_nonce = meta.query_advice(c_main.rlp2, Rotation(nonce_rot));
            rlc = rlc + c_rlp1_nonce.clone() * acc_mult.clone() * r_table[rind].clone();
            rind += 1;
            rlc = rlc + c_rlp2_nonce.clone() * acc_mult.clone() * r_table[rind].clone();
            rind += 1;

            let mut is_nonce_long = meta.query_advice(
                denoter.sel1,
                Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            if !is_s {
                is_nonce_long = meta.query_advice(
                    denoter.sel1,
                    Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND)),
                );
            }
            let mut is_balance_long = meta.query_advice(
                denoter.sel2,
                Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            if !is_s {
                is_balance_long = meta.query_advice(
                    denoter.sel2,
                    Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND)),
                );
            }

            let s_advices0_nonce = meta.query_advice(s_main.bytes[0], Rotation(nonce_rot));
            let nonce_stored = meta.query_advice(accs.s_mod_node_rlc, Rotation(nonce_rot));
            let nonce_rlc = (s_advices0_nonce.clone() + nonce_stored.clone() * r_table[0].clone()) * is_nonce_long.clone()
                + nonce_stored.clone() * (one.clone() - is_nonce_long.clone()); 
            rlc = rlc + nonce_rlc * r_table[rind].clone() * acc_mult.clone();

            let c_advices0_nonce = meta.query_advice(c_main.bytes[0], Rotation(nonce_rot));
            let balance_stored = meta.query_advice(accs.c_mod_node_rlc, Rotation(nonce_rot));
            let balance_rlc = (c_advices0_nonce.clone() + balance_stored.clone() * r_table[0].clone()) * is_balance_long.clone()
                + balance_stored.clone() * (one.clone() - is_balance_long.clone()); 
            let mut curr_r = mult_diff_nonce.clone() * acc_mult.clone();
            rlc = rlc + balance_rlc * curr_r.clone();

            let s_rlp2_storage = meta.query_advice(s_main.rlp2, Rotation(storage_codehash_rot));
            let c_rlp2_storage = meta.query_advice(c_main.rlp2, Rotation(storage_codehash_rot));

            let mult_diff_balance = meta.query_advice(accs.key.mult, Rotation(nonce_rot));
            curr_r = curr_r * mult_diff_balance;
            rlc = rlc + s_rlp2_storage * curr_r.clone();

            let storage_root_stored = meta.query_advice(accs.s_mod_node_rlc, Rotation(storage_codehash_rot));
            curr_r = curr_r * r_table[0].clone();
            rlc = rlc + storage_root_stored * curr_r.clone();

            curr_r = curr_r * r_table[31].clone();
            rlc = rlc + c_rlp2_storage * curr_r.clone();

            let codehash_stored = meta.query_advice(accs.c_mod_node_rlc, Rotation(storage_codehash_rot));
            rlc = rlc + codehash_stored * curr_r.clone() * r_table[0].clone();

            // Any rotation that lands into branch children can be used.
            let rot = -17;
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_branch_init),
                );
            }

            constraints.push((
                q_enable.clone()
                    * rlc
                    * is_branch_placeholder.clone(),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            // s(c)_mod_node_hash_rlc in placeholder branch contains hash of a drifted leaf
            // (that this value corresponds to the value in the non-placeholder branch at drifted_pos
            // is checked in branch_parallel)
            let mut mod_node_hash_rlc = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
            if !is_s {
                mod_node_hash_rlc = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
            }
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * mod_node_hash_rlc
                    * is_branch_placeholder.clone(),
                keccak_table_i,
            ));
            };

        /*
        We take the leaf RLC computed in the key row, we then add nonce/balance and storage root/codehash
        to get the final RLC of the drifted leaf. We then check whether the drifted leaf is at
        the `drifted_pos` in the parent branch - we use a lookup to check that the hash that
        corresponds to this RLC is in the parent branch at `drifted_pos` position.
        */
        meta.lookup_any("Account leaf key in added branch: drifted leaf hash in the parent branch (S)", |meta| {
            let mut constraints = vec![];
            add_constraints(meta, &mut constraints, true);
            constraints
        });
        meta.lookup_any("Account leaf key in added branch: drifted leaf hash in the parent branch (C)", |meta| {
            let mut constraints = vec![];
            add_constraints(meta, &mut constraints, false);
            constraints
        });

        /*
        Range lookups ensure that the value in the columns are all bytes (between 0 - 255).
        Note that `c_main.bytes` columns are not used.
        */
        range_lookups(
            meta,
            q_enable,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp1, s_main.rlp2, c_main.rlp1, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofVariables<F>,
        row: &Vec<u8>,
        offset: usize,
    ) {
        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len = (row[2] - 128) as usize + 3;
        mpt_config.compute_acc_and_mult(
            row,
            &mut pv.acc_s,
            &mut pv.acc_mult_s,
            0,
            len,
        );

        mpt_config.assign_acc(
            region,
            pv.acc_s,
            pv.acc_mult_s,
            F::zero(),
            F::zero(),
            offset,
        ).ok();
    }
}

