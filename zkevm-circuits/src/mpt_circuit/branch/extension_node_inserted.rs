use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{
        bytes_expr_into_rlc, compute_rlc, get_bool_constraint, get_is_extension_node,
        get_is_extension_node_even_nibbles, get_is_extension_node_long_odd_nibbles,
        get_is_extension_node_one_nibble,
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        helpers::{get_branch_len, key_len_lookup},
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM, C_RLP_START, C_START, HASH_WIDTH,
            IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_C_EXT_LONGER_THAN_55_POS, IS_C_EXT_NODE_NON_HASHED_POS,
            IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
            IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
            IS_S_EXT_LONGER_THAN_55_POS, IS_S_EXT_NODE_NON_HASHED_POS, NIBBLES_COUNTER_POS,
            RLP_NUM, ACCOUNT_LEAF_ROWS_NUM, LEAF_ROWS_NUM, EXISTING_EXT_NODE_BEFORE_S,
            EXISTING_EXT_NODE_AFTER_S,
        },
    },
    mpt_circuit::{MPTConfig, ProofValues},
    table::KeccakTable,
};

use super::BranchCols;
use super::extension::{extension_node_rlp, extension_node_rlc, extension_node_selectors};

/*
An existing extension node (which gets modified because of an inserted extension node) occupies 6 rows.
The rows are the following:
EXISTING_EXT_NODE_BEFORE_SELECTORS
EXISTING_EXT_NODE_BEFORE_S
EXISTING_EXT_NODE_BEFORE_C
EXISTING_EXT_NODE_AFTER_SELECTORS
EXISTING_EXT_NODE_AFTER_S
EXISTING_EXT_NODE_AFTER_C

This file contains constraints for the existing extension node rows which appear after the leaf rows.
Some constraints are the same as as for the extension node rows that appear in the branch rows (RLP, RLC),
some are different (extension node selectors).

It needs to be checked that the newly inserted extension node branch only has two elements:
the leaf that caused a new extension node to be added and the old extension node that drifted into
a branch of the newly added extension node.
And it needs to be ensured that the drifted extension node is the same as it was before
the modification except for the change in its key (otherwise the attacker might hide one modification
- the modification of the drifted extension node).

The constraints that are implemented in `extension_node_key.rs` are not implemented for an existing
extension node as we do not have the underlying branch and other elements down to the leaf for it.
From `extension_node_key.rs` constraints we only need to implement the constraints related
to the second nibbles.

Note that `S` and `C` hashes (values in `c_main`) in the two `before` rows are the same. Likewise for
the two `after` rows. So the constraints like RLC and RLP are checked only for `S` rows (`c_main`
in `C` rows is never used, we need `C` rows only for the second nibbles).
*/

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeInsertedConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ExtensionNodeInsertedConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Clone,
        inter_root: Column<Advice>,
        position_cols: PositionCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        branch: BranchCols<F>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        keccak_table: KeccakTable,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        is_before: bool,
        check_zeros: bool,
    ) -> Self {
        let config = ExtensionNodeInsertedConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::from(1_u64));
        let c128 = Expression::Constant(F::from(128));
        let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());
        let c192 = Expression::Constant(F::from(192));
        let rot_into_ext_node_selectors = -1;

        extension_node_rlp(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            rot_into_ext_node_selectors,
        );

        extension_node_rlc(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            accs.clone(),
            power_of_randomness.clone(),
            true,
        );
        
        extension_node_selectors(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            is_account_leaf_in_added_branch.clone(),
            rot_into_ext_node_selectors,
            true,
            true,
            is_before,
        );

        /*
        TODO: Correspondence between nibbles in C and bytes in S to be checked (for
        regular extension nodes this is done in extension_node_key.rs).
        */

        /*
        When we have an extension node in the first level of the account trie,
        its hash needs to be compared to the root of the trie.

        Note that existing extension node never appears in the first level (it can in `getProof`
        response) because the witness generator puts it after the leaf of the inserted extension
        node rows. So to check whether the existing extension node is in the first level, we need
        to check whether the inserted extension node is in the first level.
        */
        meta.lookup_any(
            "Account first level (existing) extension node hash - compared to root",
            |meta| {
                let q_enable = q_enable(meta);

                let mut rot_into_branch = - EXISTING_EXT_NODE_BEFORE_S - 1 - ACCOUNT_LEAF_ROWS_NUM;
                if !is_before {
                    rot_into_branch = - EXISTING_EXT_NODE_AFTER_S - 1 - ACCOUNT_LEAF_ROWS_NUM;
                }

                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation(rot_into_branch));

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                let selector = q_not_first * q_enable * (one.clone() - not_first_level);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc_c, keccak_input_rlc));

                let ext_len =
                    meta.query_advice(s_main.rlp1, Rotation::cur()) - c192.clone() + one.clone();

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * ext_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * root, keccak_output_rlc));

                table_map
            },
        );

        /*
        When extension node is in the first level of the storage trie, we need to check whether
        `hash(ext_node) = storage_trie_root`. We do this by checking whether
        `(ext_node_RLC, storage_trie_root_RLC)` is in the keccak table.

        Note: extension node in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        /*
        meta.lookup_any(
            "Extension node in first level of storage trie - hash compared to the storage root",
            |meta| {
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let mut rot_into_branch_init = -17;
                let mut rot_into_last_branch_child = -1;
                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                let mut is_inserted_ext_node = meta.query_advice(
                    /* rlp2 (corresponds to IS_INSERTED_EXT_NODE_C_POS) is correct here,
                    that means in S proof we have a copy (as a placeholder) of C extension node,
                    while the actual S extension node is stored in the rows below the leaf.
                    */
                    c_main.rlp2,
                    Rotation(rot_into_branch_init),
                );
                if !is_s {
                    rot_into_branch_init = -18;
                    rot_into_last_branch_child = -2;
                    is_branch_placeholder = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                    is_inserted_ext_node = meta.query_advice(
                        /* rlp1 (corresponds to IS_INSERTED_EXT_NODE_S_POS) is correct here,
                        that means in C proof we have a copy (as a placeholder) of S extension node,
                        while the actual C extension node is stored in the rows below the leaf.
                        */
                        c_main.rlp1,
                        Rotation(rot_into_branch_init),
                    );
                }

                // Only check if there is an account above the leaf.
                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_extension_node =
                    get_is_extension_node(meta, s_main.bytes, rot_into_branch_init);

                // We need to do the lookup only if we are in the last branch child.
                let is_after_last_branch_child =
                    meta.query_advice(branch.is_last_child, Rotation(rot_into_last_branch_child));

                // Note: acc_c in both cases.
                let acc = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                let mut sc_hash = vec![];
                // Note: storage root is always in `s_main.bytes`.
                for column in s_main.bytes.iter() {
                    if is_s {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND),
                            ),
                        ));
                    } else {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND),
                            ),
                        ));
                    }
                }
                let hash_rlc = bytes_expr_into_rlc(&sc_hash, power_of_randomness[0].clone());

                let selector = not_first_level
                    * is_extension_node
                    * is_after_last_branch_child
                    * is_account_leaf_in_added_branch
                    * (one.clone() - is_inserted_ext_node)
                    * (one.clone() - is_branch_placeholder);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc, keccak_input_rlc));

                let mut rot = 0;
                if !is_s {
                    rot = -1;
                }
                let ext_len =
                    meta.query_advice(s_main.rlp1, Rotation(rot)) - c192.clone() + one.clone();

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * ext_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * hash_rlc, keccak_output_rlc));

                table_map
            },
        );
        */

        /*
        Check whether the extension node hash is in the parent branch.
        That means we check whether
        `(extension_node_RLC, node_hash_RLC)` is in the keccak table where `node` is a parent
        brach child at `modified_node` position.

        Note: do not check if it is in the first storage level (see `storage_root_in_account_leaf.rs`).
        */
        /*
        meta.lookup_any("Extension node hash in parent branch", |meta| {
            let q_enable = q_enable(meta);
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

            let is_account_leaf_in_added_branch = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );

            // When placeholder extension, we don't check its hash in a parent.
            let mut is_branch_placeholder = s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
            if !is_s {
                is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
            }
            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_branch_init));

            let mut is_ext_node_non_hashed = s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM];
            if !is_s {
                is_ext_node_non_hashed = s_main.bytes[IS_C_EXT_NODE_NON_HASHED_POS - RLP_NUM];
            }
            let is_ext_node_non_hashed =
                meta.query_advice(is_ext_node_non_hashed, Rotation(rot_into_branch_init));

            let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

            // Any rotation that lands into branch can be used instead of -21.
            let mut mod_node_hash_rlc_cur = meta.query_advice(accs.s_mod_node_rlc, Rotation(-21));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(-21));
            }

            let selector = not_first_level
                * q_enable
                * (one.clone() - is_account_leaf_in_added_branch)
                * (one.clone() - is_branch_placeholder)
                * (one.clone() - is_ext_node_non_hashed);

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((selector.clone() * acc_c, keccak_input_rlc));

            let mut rot = 0;
            if !is_s {
                rot = -1;
            }
            let ext_len =
                meta.query_advice(s_main.rlp1, Rotation(rot)) - c192.clone() + one.clone();

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * ext_len, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((selector * mod_node_hash_rlc_cur, keccak_output_rlc));

            table_map
        });
        */

        /*
        meta.create_gate(
            "Extension node in parent branch (non-hashed extension node)",
            |meta| {
                let q_enable = q_enable(meta);
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                // When placeholder extension, we don't check its hash in a parent.
                let mut is_branch_placeholder = s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
                if !is_s {
                    is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
                }
                let is_branch_placeholder =
                    meta.query_advice(is_branch_placeholder, Rotation(rot_into_branch_init));

                let mut is_ext_node_non_hashed =
                    s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM];
                if !is_s {
                    is_ext_node_non_hashed = s_main.bytes[IS_C_EXT_NODE_NON_HASHED_POS - RLP_NUM];
                }
                let is_ext_node_non_hashed =
                    meta.query_advice(is_ext_node_non_hashed, Rotation(rot_into_branch_init));

                let mut constraints = vec![];

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let mut mod_node_hash_rlc_cur =
                    meta.query_advice(accs.s_mod_node_rlc, Rotation(-21));
                if !is_s {
                    mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(-21));
                }

                /*
                When an extension node is not hashed, we do not check whether it is in a parent
                branch using a lookup (see above), instead we need to check whether the branch child
                at `modified_node` position is exactly the same as the extension node.
                */
                constraints.push((
                    "Non-hashed extension node in parent branch",
                    q_not_first
                        * not_first_level
                        * q_enable
                        * (one.clone() - is_account_leaf_in_added_branch)
                        * (one.clone() - is_branch_placeholder)
                        * is_ext_node_non_hashed
                        * (mod_node_hash_rlc_cur - acc_c),
                ));

                constraints
            },
        );
        */

        /*
        We need to make sure the total number of nibbles is 64. This constraint ensures the number
        of nibbles used (stored in branch init) is correctly computed - nibbles up until this
        extension node + nibbles in this extension node.
        Once in a leaf, the remaining nibbles stored in a leaf need to be added to the count.
        The final count needs to be 64.
        */
        /*
        if is_s {
            meta.create_gate("Extension node number of nibbles", |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let q_enable = q_enable(meta);
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                // Only check if there is an account above the branch.
                let is_first_storage_level = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_ext_longer_than_55 = meta.query_advice(
                    s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );

                let is_short =
                    get_is_extension_node_one_nibble(meta, s_main.bytes, rot_into_branch_init);
                let is_even_nibbles =
                    get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_into_branch_init);
                let is_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(
                    meta,
                    s_main.bytes,
                    rot_into_branch_init,
                );

                /*
                Note: for regular branches, the constraint that `nibbles_count` increases
                by 1 is in `branch.rs`.
                */

                let nibbles_count_cur = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                let mut nibbles_count_prev = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init - BRANCH_ROWS_NUM),
                );

                /*
                nibbles_count_prev needs to be 0 when in first account level or
                in first storage level
                */
                nibbles_count_prev =
                    (one.clone() - is_first_storage_level) * nibbles_count_prev.clone();
                nibbles_count_prev = not_first_level * nibbles_count_prev.clone();

                /*
                When there is only one nibble in the extension node, `nibbles_count` changes
                for 2: one nibble and `modified_node` in a branch.
                */
                constraints.push((
                    "Nibbles number when one nibble",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_short
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - one.clone()
                            - one.clone()), // -1 for nibble, - 1 is for branch position
                ));

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
                let mut num_nibbles =
                    (s_rlp2.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone());
                /*
                When there is an even number of nibbles in the extension node,
                we compute the number of nibbles as: `(s_rlp2 - 128 - 1) * 2`.
                By `s_rlp2 - 128` we get the number of bytes where nibbles are compressed, but
                then we need to subtract 1 because `s_main.bytes[0]` does not contain any nibbles
                (it is just 0 when even number of nibbles).

                In the example below it is: `(130 - 128 - 1) * 2`.
                `[228,130,0,149,160,114,253...`
                */
                constraints.push((
                    "Nibbles number when even number of nibbles & ext not longer than 55",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_even_nibbles.clone()
                        * (one.clone() - is_ext_longer_than_55.clone())
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - num_nibbles.clone()
                            - one.clone()), // - 1 is for branch position
                ));

                num_nibbles = (s_rlp2 - c128.clone()) * (one.clone() + one.clone()) - one.clone();

                /*
                When there is an odd number of nibbles in the extension node,
                we compute the number of nibbles as: `(s_rlp2 - 128) * 2`.
                By `s_rlp2 - 128` we get the number of bytes where nibbles are compressed. We
                multiply by 2 to get the nibbles, but then subtract 1 because in
                `s_main.bytes[0]` there is only 1 nibble.
                */
                constraints.push((
                    "Nibbles num when odd number (>1) of nibbles & ext not longer than 55",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_long_odd_nibbles.clone()
                        * (one.clone() - is_ext_longer_than_55.clone())
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - num_nibbles.clone()
                            - one.clone()), // - 1 is for branch position
                ));

                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                num_nibbles =
                    (s_bytes0.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone());

                /*
                When there is an even number of nibbles in the extension node and the extension
                node is longer than 55 bytes, the number of bytes containing the nibbles
                is given by `s_main.bytes[0]`.
                We compute the number of nibbles as: `(s_bytes0 - 128 - 1) * 2`.
                By `s_bytes0 - 128` we get the number of bytes where nibbles are compressed, but
                then we need to subtract 1 because `s_main.bytes[1]` does not contain any nibbles
                (it is just 0 when even number of nibbles).
                */
                constraints.push((
                    "Nibbles num when even number of nibbles & ext longer than 55",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_even_nibbles
                        * is_ext_longer_than_55.clone()
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - num_nibbles.clone()
                            - one.clone()), // - 1 is for branch position
                ));

                num_nibbles = (s_bytes0 - c128.clone()) * (one.clone() + one.clone()) - one.clone();

                /*
                When there is an odd number of nibbles in the extension node and the extension,
                node is longer than 55 bytes, the number of bytes containing the nibbles
                is given by `s_main.bytes[0]`.
                We compute the number of nibbles as: `(s_main.bytes[0] - 128) * 2`.
                By `s_main.bytes[0] - 128` we get the number of bytes where nibbles are compressed. We
                multiply by 2 to get the nibbles, but then subtract 1 because in
                `s_main.bytes[1]` there is only 1 nibble.

                Example:
                `[248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]`
                */
                constraints.push((
                    "Nibbles num when odd number (>1) of nibbles & ext longer than 55",
                    q_not_first
                        * q_enable
                        * is_long_odd_nibbles
                        * is_ext_longer_than_55
                        * (nibbles_count_cur - nibbles_count_prev - num_nibbles - one), // - 1 is for branch position
                ));

                constraints
            });
        }
        */

        // Note: range_lookups are in extension_node_key.

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
        if pv.is_extension_node {
            // [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,
            // 48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

            // One nibble:
            // [226,16,160,172,105,12...
            // Could also be non-hashed branch:
            // [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,
            // 128,128,128,128,128,128,128,128,128]

            // [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            // 213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,
            // 128,128] [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            // 0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,
            // 128,128,128,128,128,128,128,128,128,128,128]

            // Intermediate RLC value and mult (after key)
            // to know which mult we need to use in c_advices.
            pv.acc_s = F::zero();
            pv.acc_mult_s = F::one();
            let len: usize;
            if row.get_byte(1) <= 32 {
                // key length is 1
                len = 2 // [length byte, key]
            } else if row.get_byte(0) < 248 {
                len = (row.get_byte(1) - 128) as usize + 2;
            } else {
                len = (row.get_byte(2) - 128) as usize + 3;
            }
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_s,
                &mut pv.acc_mult_s,
                0,
                len,
            );

            // Final RLC value.
            pv.acc_c = pv.acc_s;
            pv.acc_mult_c = pv.acc_mult_s;
            let mut start = C_RLP_START + 1;
            let mut len = HASH_WIDTH + 1;
            if row.get_byte(C_RLP_START + 1) == 0 {
                // non-hashed branch in extension node
                start = C_START;
                len = HASH_WIDTH;
            }
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_c,
                &mut pv.acc_mult_c,
                start,
                len,
            );

            mpt_config
                .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                .ok();

            region
                .assign_advice(
                    || "assign key_rlc".to_string(),
                    mpt_config.accumulators.key.rlc,
                    offset,
                    || Value::known(pv.extension_node_rlc),
                )
                .ok();
        }
    }
}
