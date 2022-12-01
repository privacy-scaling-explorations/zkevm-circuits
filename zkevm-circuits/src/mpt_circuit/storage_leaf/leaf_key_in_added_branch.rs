use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::branch::BranchCols,
    mpt_circuit::columns::{AccumulatorCols, MainCols},
    mpt_circuit::helpers::{
        compute_rlc, get_bool_constraint, get_is_extension_node, get_is_extension_node_one_nibble,
        mult_diff_lookup, range_lookups, get_is_inserted_extension_node
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        helpers::{get_leaf_len, key_len_lookup},
        param::{
            BRANCH_ROWS_NUM, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, LEAF_DRIFTED_IND, LEAF_KEY_C_IND,
            LEAF_KEY_S_IND,
        },
    },
    mpt_circuit::{FixedTableTag, MPTConfig, ProofValues},
    table::KeccakTable,
};

use crate::mpt_circuit::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, POWER_OF_RANDOMNESS_LEN,
    RLP_NUM,
};

/*
A storage leaf occupies 6 rows.
Contrary as in the branch rows, the `S` and `C` leaves are not positioned parallel to each other.
The rows are the following:
LEAF_KEY_S
LEAF_VALUE_S
LEAF_KEY_C
LEAF_VALUE_C
LEAF_DRIFTED
LEAF_NON_EXISTING

An example of leaf rows:
[226 160 32 235 117 17 208 2 186 74 12 134 238 103 127 37 240 27 164 245 42 218 188 162 9 151 17 57 90 177 190 250 180 61 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[27 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[225 159 63 117 31 216 242 20 172 137 89 10 84 218 35 38 178 182 67 5 68 54 127 178 216 248 46 67 173 108 157 55 18 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[225 159 59 117 17 208 2 186 74 12 134 238 103 127 37 240 27 164 245 42 218 188 162 9 151 17 57 90 177 190 250 180 61 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

The `LEAF_DRIFTED` row is nonempty when a leaf is added (or deleted) to the position in trie where there is already
an existing leaf. This appears when an existing leaf and a newly added leaf have the same initial key nibbles.
In this case, a new branch is created and both leaves (existing and newly added) appear in the new branch.
`LEAF_DRIFTED` row contains the key bytes of the existing leaf once it drifted down to the new branch.

The constraints for `LEAF_DRIFTED` row are very similar to the ones for `LEAF_KEY` rows, but we have
different selectors (different row) and there are some scenarios that do not appear here, like being in
the first level of the trie. Also, when computing the leaf RLC, we need to take a different approach because
the leaf value for the drifted leaf is stored in a parallel proof.

Note that it is important that it is ensured that only one modification has been done to the trie.
To achieve this it needs to be ensured that the new branch contains only two elements:
the leaf that was added and the old leaf that drifted into a new branch.
And it also needs to be ensured that the drifted leaf is the same as it was before the modification
except for the change in its key (otherwise the attacker might hide one modification - the modification
of the drifted leaf).
*/

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyInAddedBranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyInAddedBranchConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        branch: BranchCols<F>,
        accs: AccumulatorCols<F>,
        drifted_pos: Column<Advice>,
        is_account_leaf_in_added_branch: Column<Advice>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        keccak_table: KeccakTable,
        check_zeros: bool,
    ) -> Self {
        let config = LeafKeyInAddedBranchConfig {
            _marker: PhantomData,
        };

        let one = Expression::Constant(F::one());
        let c16 = Expression::Constant(F::from(16_u64));
        let c32 = Expression::Constant(F::from(32_u64));
        let c48 = Expression::Constant(F::from(48_u64));
        let rot_branch_init = -LEAF_DRIFTED_IND - BRANCH_ROWS_NUM;
        let rot_into_account = -LEAF_DRIFTED_IND - 1;

        /*
        Note: The leaf value is not stored in this row, but it needs to be the same
        as the leaf value before it drifted down to the new branch, so we can
        retrieve it from the row of a leaf before a drift. We need the leaf value to build the leaf RLC
        to check that the hash of a drifted leaf is in the new branch.
        */

        /*
        It needs to be ensured that the leaf intermediate RLC (containing the leaf key bytes) is properly computed.
        The intermediate RLC is then used to compute the final leaf RLC (containing the leaf value bytes too).
        Finally, the lookup is used to check that the hash that
        corresponds to the leaf RLC is in the parent branch at `drifted_pos` position.
        */
        meta.create_gate("Storage leaf in added branch RLC & inserted extension node selector", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());

            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let last_level = flag1.clone() * flag2.clone();
            let one_nibble = (one.clone() - flag1.clone()) * (one.clone() - flag2.clone());
            let is_long = flag1.clone() * (one.clone() - flag2.clone());
            let is_short = (one.clone() - flag1.clone()) * flag2.clone();

            /*
            When `is_long` (the leaf value is longer than 1 byte), `s_main.rlp1` needs to be 248.

            Example:
            `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
            */
            constraints.push((
                "is_long",
                q_enable.clone() * is_long.clone() * (s_rlp1.clone() - c248),
            ));

            /*
            The two values that store the information about what kind of case we have need to be boolean.
            */
            constraints.push((
                "flag1 is boolean",
                get_bool_constraint(q_enable.clone(), flag1),
            ));
            constraints.push((
                "flag2 is boolean",
                get_bool_constraint(q_enable.clone(), flag2),
            ));

            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );

            /*
            If leaf is in the first storage level, there cannot be a placeholder branch (it would push the
            leaf into a second level) and we do not need to trigger any checks.
            Note that in this case `is_branch_placeholder` gets some value from the account rows and we cannot use it.
            */
            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
            let rlc_last_level = s_rlp1 + s_rlp2 * power_of_randomness[0].clone();

            let mut rlc = rlc_last_level.clone()
                + compute_rlc(
                    meta,
                    s_main.bytes.to_vec(),
                    1,
                    one.clone(),
                    0,
                    power_of_randomness.clone(),
                );

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            rlc = rlc
                + c_rlp1
                    * power_of_randomness[POWER_OF_RANDOMNESS_LEN - 1].clone()
                    * power_of_randomness[1].clone();
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            rlc = rlc
                + c_rlp2
                    * power_of_randomness[POWER_OF_RANDOMNESS_LEN - 1].clone()
                    * power_of_randomness[2].clone();

            let acc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            /*
            We need to ensure that the RLC of the row is computed properly for `is_short` and
            `is_long`. We compare the computed value with the value stored in `accumulators.acc_s.rlc`.
            */
            constraints.push((
                "Leaf key acc",
                q_enable.clone()
                    * (is_short + is_long) // activate if is_short or is_long
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (rlc - acc.clone()),
            ));

            /*
            We need to ensure that the RLC of the row is computed properly for `last_level` and
            `one_nibble`. We compare the computed value with the value stored in `accumulators.acc_s.rlc`.

            `last_level` and `one_nibble` cases have one RLP byte (`s_rlp1`) and one byte (`s_rlp2`)
            where it is 32 (for `last_level`) or `48 + last_nibble` (for `one_nibble`).
            */
            constraints.push((
                "Leaf key acc last level",
                q_enable.clone()
                    * (last_level + one_nibble)
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (is_branch_s_placeholder + is_branch_c_placeholder) // drifted leaf appears only when there is a placeholder branch
                    * (rlc_last_level - acc),
            ));

            let is_mod_ext_node_before_mod_selectors_next_next = meta.query_advice(branch.is_mod_ext_node_before_mod_selectors, Rotation(2));
            let is_inserted_ext_node_s = meta.query_advice(
                c_main.rlp1,
                Rotation(rot_branch_init),
            );
            let is_inserted_ext_node_c = meta.query_advice(
                c_main.rlp2,
                Rotation(rot_branch_init),
            );

            /*
            Ensure there are inserted extension rows after storage leaf in case 
            we have a selector for `is_inserted_ext_node` enabled.
            */
            constraints.push((
                "Inserted extension node rows after storage leaf",
                q_enable
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (is_inserted_ext_node_s + is_inserted_ext_node_c)
                    * (one.clone() - is_mod_ext_node_before_mod_selectors_next_next),
            ));

            constraints
        });

        let sel_short = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let is_short = (one.clone() - flag1) * flag2;

            q_enable
                * is_short
                * (is_branch_s_placeholder + is_branch_c_placeholder)
                * (one.clone() - is_leaf_in_first_storage_level)
        };
        let sel_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let is_long = flag1 * (one.clone() - flag2);

            q_enable
                * is_long
                * (is_branch_s_placeholder + is_branch_c_placeholder)
                * (one.clone() - is_leaf_in_first_storage_level)
        };

        /*
        There are 0s in `s_main.bytes` after the last key nibble (this does not need to be checked
        for `last_level` and `one_nibble` as in these cases `s_main.bytes` are not used).
        */
        if check_zeros {
            for ind in 0..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_short,
                    ind + 1,
                    s_main.rlp2,
                    s_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_long,
                    ind,
                    s_main.bytes[0],
                    s_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
            key_len_lookup(
                meta,
                sel_long,
                32,
                s_main.bytes[0],
                c_main.rlp1,
                128,
                fixed_table,
            );
        }

        /*
        The intermediate RLC value of this row is stored in `accumulators.acc_s.rlc`.
        To compute the final leaf RLC in `LEAF_VALUE` row, we need to know the multiplier to be used
        for the first byte in the leaf value row (which is in a parallel proof).
        The multiplier is stored in `accumulators.acc_s.mult`.
        We check that the multiplier corresponds to the length of the key that is stored in `s_main.rlp2`
        for `is_short` and in `s_main.bytes[0]` for `is_long`.

        Note: `last_level` and `one_nibble` have fixed multiplier because the length of the nibbles
        in these cases is fixed.
        */
        mult_diff_lookup(
            meta,
            sel_short,
            2,
            s_main.rlp2,
            accs.acc_s.mult,
            128,
            fixed_table,
        );
        mult_diff_lookup(
            meta,
            sel_long,
            3,
            s_main.bytes[0],
            accs.acc_s.mult,
            128,
            fixed_table,
        );

        /*
        We need to ensure that the drifted leaf has the proper key RLC. It needs to be the same as the key RLC
        of this same leaf before it drifted to the new branch. The difference is that after being drifted the leaf
        has one nibble less stored in the key - `drifted_pos` nibble that is in a branch parallel to the branch
        placeholder (if it is an extension node there are more nibbles of a difference).

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

        Leaf S needs to have the same key RLC as Drifted leaf.
        Note that Leaf S key RLC is computed by taking the key RLC from Branch S and
        then adding the bytes in Leaf key S row.
        Drifted leaf RLC is computed by taking the key RLC from Added branch and
        then adding the bytes in Drifted leaf row.

        Delete case (C branch is placeholder):
          Branch S                        || Branch C
          Branch to be deleted            || Placeholder branch
          Leaf S (leaf to be deleted)     || Leaf C
          Leaf to be drifted one level up ||
        */
        meta.create_gate("Storage drifted leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_ext_node = get_is_extension_node(meta, s_main.bytes, rot_branch_init);
            let is_branch_placeholder_in_first_level = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_branch_init - 1),
            );

            /*
            We obtain the key RLC from the branch / extension node above the placeholder branch.
            We then add the remaining key nibbles that are stored in the drifted leaf key and the final RLC
            needs to be the same as the one stored in `accumulators.key.rlc` in the storage leaf key row
            (not the drifted leaf). This means the storage leaf has the same key RLC before and after
            it drifts into a new branch.

            We need the intermediate key RLC right before `drifted_pos` is added to it.
            If the branch parallel to the placeholder branch is an extension node,
            we have the intermediate RLC stored in the extension node `accumulators.key.rlc`.
            If it is a regular branch, we need to go one branch above to retrieve the RLC (if there is no level above,
            we take 0).
            */
            let key_rlc_cur = meta.query_advice(accs.key.rlc, Rotation(-LEAF_DRIFTED_IND - 1))
                * is_ext_node.clone()
                + (meta.query_advice(
                    accs.key.rlc,
                    Rotation(rot_branch_init - BRANCH_ROWS_NUM + 1),
                ) * (one.clone() - is_branch_placeholder_in_first_level.clone()))
                    * (one.clone() - is_ext_node.clone());

            /*
            Note: Branch key RLC is in the first branch child row (not in branch init). We need to go
            in the branch above the placeholder branch.
            */
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

            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let last_level = flag1.clone() * flag2.clone();
            let is_long = flag1.clone() * (one.clone() - flag2.clone());
            let is_short = (one.clone() - flag1) * flag2;

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

            /*
            We retrieve `key_rlc` from the leaf before it drifted into a newly added branch. This RLC
            need to be the same as the drifted leaf key RLC.
            */
            let leaf_key_s_rlc =
                meta.query_advice(accs.key.rlc, Rotation(-(LEAF_DRIFTED_IND - LEAF_KEY_S_IND)));
            let leaf_key_c_rlc =
                meta.query_advice(accs.key.rlc, Rotation(-(LEAF_DRIFTED_IND - LEAF_KEY_C_IND)));

            let is_leaf_in_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            // Any rotation that lands into branch children can be used.
            let drifted_pos = meta.query_advice(drifted_pos, Rotation(-17));
            let drifted_pos_mult = key_rlc_mult.clone() * c16.clone() * is_c16.clone()
                + key_rlc_mult.clone() * is_c1.clone();

            let key_rlc_start = key_rlc_cur + drifted_pos * drifted_pos_mult;

            // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[0]`.
            let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());

            /*
            If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[0]`.
            This is because `c1` in the branch above means there is an even number of nibbles left
            and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
            specifying the length) of the key is 32.

            Note: `is_c1` is taken from the branch parallel to the placeholder branch. This is because
            the leaf in added branch is in this branch (parallel to placeholder branch).
            When computing the key RLC, `is_c1` means `drifted_pos` needs to be multiplied by 1, while
            `is_c16` means `drifted_pos` needs to be multiplied by 16.
            */
            constraints.push((
                "Leaf key RLC s_bytes0 = 32 (short)",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_bytes0.clone() - c32.clone())
                    * is_c1.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * is_short.clone(),
            ));

            let mut key_rlc_short = key_rlc_start.clone()
                + (s_bytes0 - c48.clone()) * is_c16.clone() * key_rlc_mult.clone();

            for ind in 1..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_short =
                    key_rlc_short + s * key_rlc_mult.clone() * power_of_randomness[ind - 1].clone();
            }

            /*
            Note: drifted leaf key cannot reach `c_main.rlp1` because it has at most 31 nibbles.
            In case of 31 nibbles, the key occupies 32 bytes (in case of 32 nibbles and no
            branch above the leaf, the key occupies 33 bytes).
            */

            /*
            No need to distinguish between `is_c16` and `is_c1` here as it was already
            when computing `key_rlc`.
            */

            /*
            When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
            in a new branch. We retrieve it from `LEAF_KEY_S` row.
            This value needs to be the same as the key RLC of the drifted leaf.
            */
            constraints.push((
                "Drifted leaf key RLC S (short)",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * is_short.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_s_rlc.clone() - key_rlc_short.clone()),
            ));

            /*
            When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
            has been deleted (and there were only two leaves, so the branch was deleted).
            We retrieve it from `LEAF_KEY_C` row.
            This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
            the leaf that was deleted) before the leaf was deleted.
            */
            constraints.push((
                "Drifted leaf key RLC C (short)",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * is_short
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_c_rlc.clone() - key_rlc_short),
            ));

            // Long:
            // Note: long means long leaf RLP, not extension node nibbles.

            // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[1]`.
            let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());

            /*
            If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[1]`.
            This is because `is_c1` in the branch above means there is an even number of nibbles left
            and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
            specifying the length) of the key is 32.
            */
            constraints.push((
                "Leaf key acc s_bytes1 = 32 (long)",
                q_enable.clone()
                    * (s_bytes1.clone() - c32.clone())
                    * is_c1
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * is_long.clone(),
            ));

            let mut key_rlc_long =
                key_rlc_start.clone() + (s_bytes1 - c48.clone()) * is_c16 * key_rlc_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_mult = key_rlc_mult * power_of_randomness[0].clone();
                key_rlc_long = key_rlc_long + s * key_rlc_mult.clone();
            }

            key_rlc_mult = key_rlc_mult * power_of_randomness[0].clone();
            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            key_rlc_long = key_rlc_long + c_rlp1 * key_rlc_mult.clone();

            /*
            When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
            in a new branch. We retrieve it from `LEAF_KEY_S` row.
            This value needs to be the same as the key RLC of the drifted leaf.
            */
            constraints.push((
                "Drifted leaf key RLC S (long)",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * is_long.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_s_rlc.clone() - key_rlc_long.clone()),
            ));

            /*
            When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
            has been deleted (and there were only two leaves, so the branch was deleted).
            We retrieve it from `LEAF_KEY_C` row.
            This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
            the leaf that was deleted) before the leaf was deleted.
            */
            constraints.push((
                "Drifted leaf key RLC C (long)",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * is_long
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_c_rlc.clone() - key_rlc_long),
            ));

            // Last level:
            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());

            /*
            When the leaf is in the last level there are no nibbles stored in the key and `s_main.rlp2 = 32`.
            */
            constraints.push((
                "Leaf key acc s_rlp2 = 32 (last level)",
                q_enable.clone()
                    * (is_branch_s_placeholder.clone() + is_branch_c_placeholder.clone()) // drifted leaf appears only when there is a placeholder branch
                    * (s_rlp2.clone() - c32.clone())
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * last_level.clone(),
            ));

            /*
            When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
            in a new branch. We retrieve it from `LEAF_KEY_S` row.
            This value needs to be the same as the key RLC of the drifted leaf.

            We do not need to add any nibbles to the key RLC as there are none stored in the storage leaf
            (last level).
            */
            constraints.push((
                "Drifted leaf key RLC S (last level)",
                q_enable.clone()
                    * is_branch_s_placeholder.clone()
                    * last_level.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_s_rlc.clone() - key_rlc_start.clone()), /* no nibbles in drifted
                                                                         * leaf */
            ));

            /*
            When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
            has been deleted (and there were only two leaves, so the branch was deleted).
            We retrieve it from `LEAF_KEY_C` row.
            This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
            the leaf that was deleted) before the leaf was deleted.

            We do not need to add any nibbles to the key RLC as there are none stored in the storage leaf
            (last level).
            */
            constraints.push((
                "Drifted leaf key RLC C (last level)",
                q_enable.clone()
                    * is_branch_c_placeholder.clone()
                    * last_level.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_c_rlc.clone() - key_rlc_start.clone()), /* no nibbles in drifted
                                                                         * leaf */
            ));

            let key_rlc_one_nibble = key_rlc_start + (s_rlp2 - c48.clone()) * key_rlc_mult;

            /*
            When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
            in a new branch. We retrieve it from `LEAF_KEY_S` row.
            This value needs to be the same as the key RLC of the drifted leaf.

            We only need to add one nibble to the key RLC.
            */
            constraints.push((
                "Drifted leaf key RLC S (one nibble)",
                q_enable.clone()
                    * is_branch_s_placeholder
                    * last_level.clone()
                    * (one.clone() - is_leaf_in_first_storage_level.clone())
                    * (leaf_key_s_rlc - key_rlc_one_nibble.clone()),
            ));

            /*
            When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
            has been deleted (and there were only two leaves, so the branch was deleted).
            We retrieve it from `LEAF_KEY_C` row.
            This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
            the leaf that was deleted) before the leaf was deleted.

            We only need to add one nibble to the key RLC.
            */
            constraints.push((
                "Drifted leaf key RLC C (one nibble)",
                q_enable
                    * is_branch_c_placeholder
                    * last_level
                    * (one.clone() - is_leaf_in_first_storage_level)
                    * (leaf_key_c_rlc - key_rlc_one_nibble),
            ));

            constraints
        });

        /*
        It needs to be ensured that the hash of the drifted leaf is in the parent branch
        at `drifted_pos` position.

        Rows:
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

        We need to compute the RLC of the drifted leaf. We compute the intermediate RLC
        from the bytes in `LEAF_DRIFTED` row. And we retrieve the value from `LEAF_VALUE_S` row
        (where there is the same leaf, but before it drifted down into a new branch).

        Then we execute the lookup into a keccak table: `lookup(leaf_rlc, branch_child_at_drifted_pos_rlc)`.
        */
        meta.lookup_any(
            "Leaf key in added branch: neighbour leaf in the added branch (S)",
            |meta| {
                let q_enable = q_enable(meta);

                let mut rlc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
                let acc_mult = meta.query_advice(accs.acc_s.mult, Rotation::cur());

                // If branch placeholder in `S`, the leaf value is 3 rows above.
                let rot_val = -3;

                let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation(rot_val));
                rlc = rlc + s_rlp1 * acc_mult.clone();

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation(rot_val));
                rlc = rlc + s_rlp2 * acc_mult.clone() * power_of_randomness[0].clone();

                // TODO: use already computed RLC value in leaf row
                rlc = rlc
                    + compute_rlc(
                        meta,
                        s_main.bytes.to_vec(),
                        1,
                        acc_mult,
                        rot_val,
                        power_of_randomness.clone(),
                    );
                // Note: value does not reach c_rlp1.

                let is_leaf_in_first_storage_level =
                    meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

                // Any rotation that lands into branch children can be used.
                let rot = -17;
                let is_branch_s_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_branch_init),
                );
            
                /*
                When extension node is inserted, the leaf is only a placeholder (as well as branch) -
                the constraints for this case are in `extension_node_inserted.rs`.
                */
                let is_c_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_branch_init, true);
                let is_s_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_branch_init, false);

                /*
                `s_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                This is because `c_mod_node_hash_rlc` in the added branch stores the hash of
                `modified_node` (the leaf that has been added):

                Add case (S branch is placeholder):
                  Branch S           || Branch C
                  Placeholder branch (`s_mod_node_hash_rlc` stores `drifted_pos` node hash) || Added branch (`c_mod_node_hash_rlc` stores `modified_node` hash)
                  Leaf S             || Leaf C
                                     || Drifted leaf (this is Leaf S drifted into Added branch)

                That the stored value corresponds to the value in the non-placeholder branch at `drifted_pos`
                is checked in `branch_parallel.rs`.
                */
                let s_mod_node_hash_rlc = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));

                let selector = q_enable
                    * is_branch_s_placeholder
                    * (one.clone() - is_s_inserted_ext_node - is_c_inserted_ext_node)
                    * (one.clone() - is_leaf_in_first_storage_level);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * rlc, keccak_input_rlc));

                let rot_into_leaf_key = 0;
                let len = get_leaf_len(meta, s_main.clone(), accs.clone(), rot_into_leaf_key);

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * s_mod_node_hash_rlc, keccak_output_rlc));

                table_map
            },
        );

        /*
        It needs to be ensured that the hash of the drifted leaf is in the parent branch
        at `drifted_pos` position.

        Rows:
        Leaf key S
        Leaf value S
        Leaf key C
        Leaf value C
        Drifted leaf (leaf in added branch)

        Delete case (C branch is placeholder):
          Branch S                        || Branch C
          Branch to be deleted            || Placeholder branch
          Leaf S (leaf to be deleted)     || Leaf C
          Leaf to be drifted one level up ||

        We need to compute the RLC of the leaf that is a neighbour leaf of the leaf that is to be deleted.
        We compute the intermediate RLC from the bytes in `LEAF_DRIFTED` row.
        And we retrieve the value from `LEAF_VALUE_C` row
        (where there is the same leaf, but after it was moved one level up because of the deleted branch).

        Then we execute the lookup into a keccak table: `lookup(leaf_rlc, branch_child_at_drifted_pos_rlc)`.
        */
        meta.lookup_any(
            "Leaf key in added branch: neighbour leaf in the deleted branch (C)",
            |meta| {
                let q_enable = q_enable(meta);

                let mut rlc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
                let acc_mult = meta.query_advice(accs.acc_s.mult, Rotation::cur());

                // If branch placeholder in C, value is 1 above.
                let rot_val = -1;

                let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation(rot_val));
                rlc = rlc + s_rlp1 * acc_mult.clone();

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation(rot_val));
                rlc = rlc + s_rlp2 * acc_mult.clone() * power_of_randomness[0].clone();

                rlc = rlc
                    + compute_rlc(
                        meta,
                        s_main.bytes.to_vec(),
                        1,
                        acc_mult,
                        rot_val,
                        power_of_randomness.clone(),
                    );
                // Note: value does not reach `c_rlp1`.

                let is_leaf_in_first_storage_level =
                    meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

                // Any rotation that lands into branch children can be used.
                let rot = -17;
                let is_branch_c_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(-23),
                );

                /*
                When extension node is inserted, the leaf is only a placeholder (as well as branch) -
                the constraints for this case are in `extension_node_inserted.rs`.
                */
                let is_c_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_branch_init, true);
                let is_s_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_branch_init, false);

                /*
                `c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                This is because `s_mod_node_hash_rlc` in the deleted branch stores the hash of
                `modified_node` (the leaf that is to be deleted):

                Delete case (C branch is placeholder):
                  Branch S                        || Branch C
                  Branch to be deleted (`s_mod_node_hash_rlc` stores `modified_node` hash) || Placeholder branch (`c_mod_node_hash_rlc` stores `drifted_pos` node hash)
                  Leaf S (leaf to be deleted)     || Leaf C
                  Leaf to be drifted one level up ||

                That the stored value corresponds to the value in the non-placeholder branch at `drifted_pos`
                is checked in `branch_parallel.rs`.
                */
                let c_mod_node_hash_rlc = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));

                let selector = q_enable
                    * is_branch_c_placeholder
                    * (one.clone() - is_s_inserted_ext_node - is_c_inserted_ext_node)
                    * (one.clone() - is_leaf_in_first_storage_level);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * rlc, keccak_input_rlc));

                let rot_into_leaf_key = 0;
                let len = get_leaf_len(meta, s_main.clone(), accs.clone(), rot_into_leaf_key);

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * c_mod_node_hash_rlc, keccak_output_rlc));

                table_map
            },
        );

        /*
        Range lookups ensure that `s_main`, `c_main.rlp1`, `c_main.rlp2` columns are all bytes (between 0 - 255).
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
        row: &MptWitnessRow<F>,
        offset: usize,
    ) {
        /*
        row[1] != 0 just to avoid usize problems below (when row doesn't
        need to be assigned) Info whether leaf rlp is long or short.
        */
        let mut typ = "short";
        if row.get_byte(0) == 248 {
            typ = "long";
        } else if row.get_byte(1) == 32 {
            typ = "last_level";
        }
        mpt_config.assign_long_short(region, typ, offset).ok();
        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len = if row.get_byte(0) == 248 {
            (row.get_byte(2) - 128) as usize + 3
        } else {
            (row.get_byte(1) - 128) as usize + 2
        };
        mpt_config.compute_acc_and_mult(&row.bytes, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

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
