use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::branch::BranchCols,
    mpt_circuit::columns::{AccumulatorCols, DenoteCols, MainCols},
    mpt_circuit::helpers::{
        compute_rlc, get_is_extension_node, get_is_extension_node_one_nibble, mult_diff_lookup,
        range_lookups,
    },
    mpt_circuit::param::{
        ACCOUNT_DRIFTED_LEAF_IND, ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND,
        ACCOUNT_LEAF_NONCE_BALANCE_C_IND, ACCOUNT_LEAF_NONCE_BALANCE_S_IND,
        ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM,
        IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
    },
    mpt_circuit::{helpers::{key_len_lookup, get_is_inserted_extension_node}, FixedTableTag, MPTConfig, ProofValues},
    table::KeccakTable,
};

use crate::mpt_circuit::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, POWER_OF_RANDOMNESS_LEN,
    RLP_NUM,
};

/*
An account leaf occupies 8 rows.
Contrary as in the branch rows, the `S` and `C` leaves are not positioned parallel to each other.
The rows are the following:
ACCOUNT_LEAF_KEY_S
ACCOUNT_LEAF_KEY_C
ACCOUNT_NON_EXISTING
ACCOUNT_LEAF_NONCE_BALANCE_S
ACCOUNT_LEAF_NONCE_BALANCE_C
ACCOUNT_LEAF_STORAGE_CODEHASH_S
ACCOUNT_LEAF_STORAGE_CODEHASH_C
ACCOUNT_DRIFTED_LEAF

An example of leaf rows:
[248 102 157 55 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 6]
[248 102 157 32 133 130 180 167 143 97 28 115 102 25 94 62 148 249 8 6 55 244 16 75 187 208 208 127 251 120 61 73 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4]
[0 0 157 32 133 130 180 167 143 97 28 115 102 25 94 62 148 249 8 6 55 244 16 75 187 208 208 127 251 120 61 73 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 18]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 23 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 8]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 9]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 11]
[248 102 157 32 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 6 10]

The `ACCOUNT_LEAF_DRIFTED` row is nonempty when a leaf is added (or deleted) to the position in trie where there is already
an existing leaf. This appears when an existing leaf and a newly added leaf have the same initial key nibbles.
In this case, a new branch is created and both leaves (existing and newly added) appear in the new branch.
`ACCOUNT_LEAF_DRIFTED` row contains the key bytes of the existing leaf once it drifted down to the new branch.

Note that it is important that it is ensured that only one modification has been done to the trie.
To achieve this it needs to be ensured that the new branch contains only two elements:
the leaf that was added and the old leaf that drifted into a new branch.
And it also needs to be ensured that the drifted leaf is the same as it was before the modification
except for the change in its key (otherwise the attacker might hide one modification - the modification
of the drifted leaf).
*/

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyInAddedBranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyInAddedBranchConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        not_first_level: Column<Advice>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        branch: BranchCols<F>,
        accs: AccumulatorCols<F>, /* accs.acc_c contains mult_diff_nonce, initially key_rlc was
                                   * used for mult_diff_nonce, but it caused PoisonedConstraint
                                   * in extension_node_key */
        drifted_pos: Column<Advice>,
        denoter: DenoteCols<F>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        keccak_table: KeccakTable,
        check_zeros: bool,
    ) -> Self {
        let config = AccountLeafKeyInAddedBranchConfig {
            _marker: PhantomData,
        };

        /*
        Note: `q_enable` switches off the first level, there is no need for checks
        for the first level because when the leaf appears in an added branch it is at least
        in the second level (added branch being above it).
        */

        let one = Expression::Constant(F::one());
        let c16 = Expression::Constant(F::from(16_u64));
        let c32 = Expression::Constant(F::from(32_u64));
        let c48 = Expression::Constant(F::from(48_u64));
        let rot_branch_init = -ACCOUNT_DRIFTED_LEAF_IND - BRANCH_ROWS_NUM;

        meta.create_gate(
            "Account drifted leaf: intermediate leaf RLC after key & inserted extension node selector",
            |meta| {
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
                let mut expr = s_rlp1
                    + meta.query_advice(s_main.rlp2, Rotation::cur())
                        * power_of_randomness[ind].clone();
                ind += 1;

                expr = expr
                    + compute_rlc(
                        meta,
                        s_main.bytes.to_vec(),
                        ind,
                        one.clone(),
                        0,
                        power_of_randomness.clone(),
                    );

                let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                expr = expr
                    + c_rlp1
                        * power_of_randomness[POWER_OF_RANDOMNESS_LEN - 1].clone()
                        * power_of_randomness[1].clone();
                expr = expr
                    + c_rlp2
                        * power_of_randomness[POWER_OF_RANDOMNESS_LEN - 1].clone()
                        * power_of_randomness[2].clone();

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
                constraints.push((
                    "Account leaf key intermediate RLC",
                    q_enable.clone()
                        * (is_branch_s_placeholder + is_branch_c_placeholder) // drifted leaf appears only when there is a placeholder branch
                        * (expr - acc),
                ));
                 
                let is_mod_ext_node_before_mod_selectors_next = meta.query_advice(branch.is_mod_ext_node_before_mod_selectors, Rotation(1));
                let is_inserted_ext_node_s = meta.query_advice(
                    c_main.rlp1,
                    Rotation(rot_branch_init),
                );
                let is_inserted_ext_node_c = meta.query_advice(
                    c_main.rlp2,
                    Rotation(rot_branch_init),
                );

                /*
                Ensure there are inserted extension rows after account leaf in case 
                we have a selector for `is_inserted_ext_node` enabled.
                */
                constraints.push((
                    "Inserted extension node rows after account leaf",
                    q_enable
                        * (is_inserted_ext_node_s + is_inserted_ext_node_c)
                        * (one.clone() - is_mod_ext_node_before_mod_selectors_next),
                ));

                constraints
            },
        );

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
        Similarly as in account_leaf_key.rs,
        key RLC is computed over `s_main.bytes[1]`, ..., `s_main.bytes[31]` because we do not know
        the key length in advance. To prevent changing the key and setting `s_main.bytes[i]` for
        `i > nonce_len + 1` to get the desired nonce RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.
        The key can also appear in `c_main.rlp1` and `c_main.rlp2`, so we need to check these two columns too.
        */
        if check_zeros {
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
            key_len_lookup(
                meta,
                sel,
                32,
                s_main.bytes[0],
                c_main.rlp1,
                128,
                fixed_table,
            );
            key_len_lookup(
                meta,
                sel,
                33,
                s_main.bytes[0],
                c_main.rlp2,
                128,
                fixed_table,
            );
        }

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
        mult_diff_lookup(
            meta,
            sel,
            3,
            s_main.bytes[0],
            accs.acc_s.mult,
            128,
            fixed_table,
        );

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
        Note that Leaf S RLC is computed by taking the key RLC from Branch S and then adding
        the bytes in Leaf key S row.
        Drifted leaf RLC is computed by taking the key RLC from Added branch and then adding the bytes
        in Drifted leaf row.

        Delete case (C branch is placeholder):
          Branch S                        || Branch C
          Branch to be deleted            || Placeholder branch
          Leaf S (leaf to be deleted)     || Leaf C
          Leaf to be drifted one level up ||
        */
        meta.create_gate("Account drifted leaf key RLC", |meta| {
            // Drifted leaf in added branch has the same key as it had it before it drifted
            // down to the new branch.
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_ext_node = get_is_extension_node(meta, s_main.bytes, rot_branch_init);
            let is_branch_placeholder_in_first_level =
                one.clone() - meta.query_advice(not_first_level, Rotation(rot_branch_init));

            /*
            We obtain the key RLC from the branch / extension node above the placeholder branch.
            We then add the remaining key nibbles that are stored in the drifted leaf key and the final RLC
            needs to be the same as the one stored in `accumulators.key.rlc` in the account leaf key row
            (not the drifted leaf). This means the storage leaf has the same key RLC before and after
            it drifts into a new branch.

            Note: Branch key RLC is in the first branch child row (not in branch init). We need to go
            in the branch above the placeholder branch.
            */

            /*
            We need the intermediate key RLC right before `drifted_pos` is added to it. If the branch parallel to the placeholder branch
            is an extension node, we have the intermediate RLC stored in the extension node `accumulators.key.rlc`.
            If it is a regular branch, we need to go one branch above to retrieve the RLC (if there is no level above, we take 0).
            */
            let key_rlc_cur = meta
                .query_advice(accs.key.rlc, Rotation(-ACCOUNT_DRIFTED_LEAF_IND - 1))
                * is_ext_node.clone()
                + (meta.query_advice(
                    accs.key.rlc,
                    Rotation(rot_branch_init - BRANCH_ROWS_NUM + 1),
                ) * (one.clone() - is_branch_placeholder_in_first_level.clone()))
                    * (one.clone() - is_ext_node.clone());

            let branch_above_placeholder_mult = meta.query_advice(
                accs.key.mult,
                Rotation(rot_branch_init - BRANCH_ROWS_NUM + 1),
            ) * (one.clone()
                - is_branch_placeholder_in_first_level.clone())
                + is_branch_placeholder_in_first_level;

            // When we have only one nibble in the extension node, `mult_diff` is not used
            // (and set).
            let is_one_nibble =
                get_is_extension_node_one_nibble(meta, s_main.bytes, rot_branch_init);

            /*
            `is_c16` and `is_c1` determine whether `drifted_pos` needs to be multiplied by 16 or 1.
            */
            let is_c16 = meta.query_advice(
                s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_c1 = meta.query_advice(
                s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            /*
            `mult_diff` is the power of multiplier `r` and it corresponds to the number of nibbles in the extension node.
            We need `mult_diff` because there is nothing stored in
            `meta.query_advice(accs.key.mult, Rotation(-ACCOUNT_DRIFTED_LEAF_IND-1))` as we always use `mult_diff` in `extension_node_key.rs`.
            */
            let mult_diff = meta.query_advice(accs.mult_diff, Rotation(rot_branch_init + 1));
            let mut key_rlc_mult = branch_above_placeholder_mult.clone()
                * mult_diff
                * is_ext_node.clone()
                * (one.clone() - is_one_nibble.clone())
                + branch_above_placeholder_mult.clone()
                    * is_ext_node.clone()
                    * is_one_nibble.clone()
                    * is_c1.clone()
                + branch_above_placeholder_mult.clone()
                    * is_ext_node.clone()
                    * is_one_nibble
                    * power_of_randomness[0].clone()
                    * is_c16.clone()
                + branch_above_placeholder_mult * (one.clone() - is_ext_node);

            /*
            Key RLC of the drifted leaf needs to be the same as key RLC of the leaf
            before it drifted down into extension/branch.
            */
            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            let leaf_key_s_rlc = meta.query_advice(
                accs.key.rlc,
                Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            let leaf_key_c_rlc = meta.query_advice(
                accs.key.rlc,
                Rotation(-(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND)),
            );

            // Any rotation that lands into branch children can be used.
            let drifted_pos = meta.query_advice(drifted_pos, Rotation(-17));
            let drifted_pos_mult = key_rlc_mult.clone() * c16.clone() * is_c16.clone()
                + key_rlc_mult.clone() * is_c1.clone();

            let key_rlc_start = key_rlc_cur + drifted_pos * drifted_pos_mult;

            // If is_c16 = 1, we have one nibble+48 in `s_main.bytes[1]`.
            let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());

            // If is_c1 = 1, we have 32 in `s_main.bytes[1]`.
            constraints.push((
                "Leaf key acc s_bytes1",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_bytes1.clone() - c32.clone())
                    * is_c1,
            ));

            let mut key_rlc =
                key_rlc_start + (s_bytes1 - c48.clone()) * is_c16 * key_rlc_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_mult = key_rlc_mult * power_of_randomness[0].clone();
                key_rlc = key_rlc + s * key_rlc_mult.clone();
            }

            key_rlc_mult = key_rlc_mult * power_of_randomness[0].clone();
            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            key_rlc = key_rlc + c_rlp1 * key_rlc_mult.clone();

            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            key_rlc = key_rlc + c_rlp2 * key_rlc_mult * power_of_randomness[0].clone();

            /*
            Note: no need to distinguish between `is_c16` and `is_c1` here as it was already
            when computing `key_rlc`.
            */

            /*
            The key RLC of the drifted leaf needs to be the same as the key RLC of the leaf before
            the drift - the nibbles are the same in both cases, the difference is that before the
            drift some nibbles are stored in the leaf key, while after the drift these nibbles are used as
            position in a branch or/and nibbles of the extension node.
            */
            constraints.push((
                "Drifted leaf key RLC same as the RLC of the leaf before drift (placeholder S)",
                q_enable.clone() * is_branch_s_placeholder * (leaf_key_s_rlc - key_rlc.clone()),
            ));
            constraints.push((
                "Drifted leaf key RLC same as the RLC of the leaf before drift (placeholder C)",
                q_enable * is_branch_c_placeholder * (leaf_key_c_rlc - key_rlc),
            ));

            constraints
        });

        let add_constraints = |meta: &mut VirtualCells<F>,
                               constraints: &mut Vec<(Expression<F>, Expression<F>)>,
                               is_s: bool| {
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
            let mut storage_codehash_rot =
                -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND);
            if !is_s {
                storage_codehash_rot =
                    -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND);
            }

            let mult_diff_nonce = meta.query_advice(accs.acc_c.rlc, Rotation(nonce_rot));

            let s_rlp1_nonce = meta.query_advice(s_main.rlp1, Rotation(nonce_rot));
            rlc = rlc + s_rlp1_nonce * acc_mult.clone();

            let s_rlp2_nonce = meta.query_advice(s_main.rlp2, Rotation(nonce_rot));
            let mut rind = 0;

            rlc = rlc + s_rlp2_nonce * acc_mult.clone() * power_of_randomness[rind].clone();
            rind += 1;

            let c_rlp1_nonce = meta.query_advice(c_main.rlp1, Rotation(nonce_rot));
            let c_rlp2_nonce = meta.query_advice(c_main.rlp2, Rotation(nonce_rot));
            rlc = rlc + c_rlp1_nonce * acc_mult.clone() * power_of_randomness[rind].clone();
            rind += 1;
            rlc = rlc + c_rlp2_nonce * acc_mult.clone() * power_of_randomness[rind].clone();
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
            let nonce_rlc = (s_advices0_nonce
                + nonce_stored.clone() * power_of_randomness[0].clone())
                * is_nonce_long.clone()
                + nonce_stored * (one.clone() - is_nonce_long);
            rlc = rlc + nonce_rlc * power_of_randomness[rind].clone() * acc_mult.clone();

            let c_advices0_nonce = meta.query_advice(c_main.bytes[0], Rotation(nonce_rot));
            let balance_stored = meta.query_advice(accs.c_mod_node_rlc, Rotation(nonce_rot));
            let balance_rlc = (c_advices0_nonce
                + balance_stored.clone() * power_of_randomness[0].clone())
                * is_balance_long.clone()
                + balance_stored * (one.clone() - is_balance_long);
            let mut curr_r = mult_diff_nonce * acc_mult;
            rlc = rlc + balance_rlc * curr_r.clone();

            let s_rlp2_storage = meta.query_advice(s_main.rlp2, Rotation(storage_codehash_rot));
            let c_rlp2_storage = meta.query_advice(c_main.rlp2, Rotation(storage_codehash_rot));

            let mult_diff_balance = meta.query_advice(accs.key.mult, Rotation(nonce_rot));
            curr_r = curr_r * mult_diff_balance;
            rlc = rlc + s_rlp2_storage * curr_r.clone();

            let storage_root_stored =
                meta.query_advice(accs.s_mod_node_rlc, Rotation(storage_codehash_rot));
            curr_r = curr_r * power_of_randomness[0].clone();
            rlc = rlc + storage_root_stored * curr_r.clone();

            curr_r = curr_r * power_of_randomness[31].clone();
            rlc = rlc + c_rlp2_storage * curr_r.clone();

            let codehash_stored =
                meta.query_advice(accs.c_mod_node_rlc, Rotation(storage_codehash_rot));
            rlc = rlc + codehash_stored * curr_r * power_of_randomness[0].clone();

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

            /*
            When extension node is inserted, the leaf is only a placeholder (as well as branch) -
            the constraints for this case are in `extension_node_inserted.rs`.
            */
            let is_c_inserted_ext_node = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_branch_init, true);
            let is_s_inserted_ext_node = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_branch_init, false);


            let selector = q_enable
                * (one.clone() - is_s_inserted_ext_node - is_c_inserted_ext_node)
                * is_branch_placeholder;

            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            constraints.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            constraints.push((selector.clone() * rlc, keccak_input_rlc));

            let account_len =
                meta.query_advice(s_main.rlp2, Rotation::cur()) + one.clone() + one.clone();

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            constraints.push((selector.clone() * account_len, keccak_input_len));

            /*
            `s(c)_mod_node_hash_rlc` in placeholder branch contains hash of a drifted leaf
            (that this value corresponds to the value in the non-placeholder branch at `drifted_pos`
            is checked in `branch_parallel.rs`)
            */
            let mut mod_node_hash_rlc = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
            if !is_s {
                mod_node_hash_rlc = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
            }

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            constraints.push((selector * mod_node_hash_rlc, keccak_output_rlc));
        };

        /*
        We take the leaf RLC computed in the key row, we then add nonce/balance and storage root/codehash
        to get the final RLC of the drifted leaf. We then check whether the drifted leaf is at
        the `drifted_pos` in the parent branch - we use a lookup to check that the hash that
        corresponds to this RLC is in the parent branch at `drifted_pos` position.
        */
        meta.lookup_any(
            "Account leaf key in added branch: drifted leaf hash in the parent branch (S)",
            |meta| {
                let mut constraints = vec![];
                add_constraints(meta, &mut constraints, true);
                constraints
            },
        );
        meta.lookup_any(
            "Account leaf key in added branch: drifted leaf hash in the parent branch (C)",
            |meta| {
                let mut constraints = vec![];
                add_constraints(meta, &mut constraints, false);
                constraints
            },
        );

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
        pv: &mut ProofValues<F>,
        row: &[u8],
        offset: usize,
    ) {
        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len = (row[2] - 128) as usize + 3;
        mpt_config.compute_acc_and_mult(row, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

        mpt_config
            .assign_acc(
                region,
                pv.acc_s,
                pv.acc_mult_s,
                F::zero(),
                F::zero(),
                offset,
            )
            .ok();
    }
}
