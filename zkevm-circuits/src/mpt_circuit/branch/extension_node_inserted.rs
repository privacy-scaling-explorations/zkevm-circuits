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
        get_is_extension_node_one_nibble, get_branch_len, key_len_lookup, get_is_inserted_extension_node,
        range_lookups,
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM, C_RLP_START, C_START, HASH_WIDTH,
            IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_C_EXT_LONGER_THAN_55_POS, IS_C_EXT_NODE_NON_HASHED_POS,
            IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
            IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
            IS_S_EXT_LONGER_THAN_55_POS, IS_S_EXT_NODE_NON_HASHED_POS, NIBBLES_COUNTER_POS,
            RLP_NUM, ACCOUNT_LEAF_ROWS_NUM, LEAF_ROWS_NUM, LONG_EXT_NODE_S,
            SHORT_EXT_NODE_S, SHORT_EXT_NODE_SELECTORS, LONG_EXT_NODE_C,
            LONG_EXT_NODE_SELECTORS, EXTENSION_ROWS_NUM,
        },
    },
    mpt_circuit::{MPTConfig, ProofValues, FixedTableTag},
    table::KeccakTable,
};

use super::BranchCols;
use super::extension::{extension_node_rlp, extension_node_rlc, extension_node_selectors, check_intermediate_mult};

/*
A modified extension node (which gets modified because of an inserted or deleted extension node)
occupies 6 rows. The rows are the following:
LONG_EXT_NODE_SELECTORS
LONG_EXT_NODE_S
LONG_EXT_NODE_C
SHORT_EXT_NODE_SELECTORS
SHORT_EXT_NODE_S
SHORT_EXT_NODE_C

This file contains constraints for the modified extension node rows which appear after the leaf rows.
Extension node is positioned after the leaf rows in case when its nibbles get elongated or shortened
because another extension node is deleted or inserted.

Insert case

Example:
We have four keys set in the trie.

key0 =  0x1000000000000000000000000000000000000000000000000000000000000000
key00 = 0x0000000000000000000000000000000000000000000000000000000000000000
key1 =  0x1234561000000000000000000000000000000000000000000000000000000000
key2 =  0x1234563000000000000000000000000000000000000000000000000000000000

We have a branch in the trie root, we have a leaf at position 0 in this branch, and we have
a branch (let us denote it by Branch1) at position 1. In this second branch (Branch1) we
have a leaf at position 0 (key0) and we have an extension node (ExtNode1) at position 2.
This extension node has nibbles [3, 4, 5, 6].

Now we add another key to the trie:
key3 = 0x1234400000000000000000000000000000000000000000000000000000000000

The extension node ExtNode1 is now in Branch1 at position 2 replaced by a new
extension node (ExtNode2) which has nibbles [3, 4]. ExtNode2 has now an extension
node at 5 - this is where ExtNode1 drifted (and now only has one nibble: 6),
let us denoted the drifted ExtNode1 by ExtNode3.
At position 4, ExtNode2 has key3. 

The terminology used for the modified extension node is:
ExtNode1 (nibbles [3, 4, 5, 6]) is named `long`.
ExtNode3 (ExtNode1 drifted into a branch of ExtNode2) is named `short` (only has one nibble: 6).
ExtNode2 (nibbles [3, 4]) is named `middle`.

The nibbles of `middle` extension node ([3, 4]) together with `drifted_pos`
of the ExtNode1 ([5]) and with drifted ExtNode1 nibbles ([6]) should be the same
as nibbles of ExtNode1 ([3, 4, 5, 6]).

It needs to be checked that the newly inserted extension node branch only has two elements:
the leaf that caused a new extension node to be added and the old extension node that drifted into
a branch of the newly added extension node (this is checked by branch constraints whenever
we have a placeholder branch, so in the case of modified extension node too).

It needs to be ensured that the drifted extension node is the same as it was before
the modification - except for the change in its nibbles (otherwise the attacker might hide
a modification - the modification of the drifted extension node).

The two extension node rows in branch rows only support cases where the nibbles of `S` and `C`
extension nodes are the same. This is why we add rows for the modified extension node after
the leaf rows (rows after leaf would be needed in any case).

Note that the branch rows above the leaf contain the branch of `middle` extension node
and a placeholder branch. We do not have `long` extension node and its branch stored anywhere
above the leaf. Instead, it is stored in `LONG_EXT_NODE_S` row (`LONG_EXT_NODE_C` is used
only for the second nibbles). We need to ensure that the hash of `long` extension node
is at `modified_node` position in the branch above `middle` rows in `S` proof.
`SHORT_EXT_NODE_S` rows contain `short` extension node. We need to ensure that
its hash is at `drifted_pos` in `middle` branch.

The constraints that are implemented in `extension_node_key.rs` are not implemented for a modified
extension node as we do not have the underlying branch and other elements down to the leaf.
From `extension_node_key.rs` constraints we only need to implement the constraints related
to the second nibbles.

---

Delete case

Example:
We have five keys set in the trie.

key0 =  0x1000000000000000000000000000000000000000000000000000000000000000
key00 = 0x0000000000000000000000000000000000000000000000000000000000000000
key1 =  0x1234561000000000000000000000000000000000000000000000000000000000
key2 =  0x1234563000000000000000000000000000000000000000000000000000000000
key3 =  0x1234400000000000000000000000000000000000000000000000000000000000

We have a branch in the trie root, we have a leaf at position 0 in this branch, and we have
a branch (let us denote it by Branch1) at position 1. In this second branch (Branch1) we
have a leaf at position 0 (key0) and we have an extension node (ExtNode2) at position 2.
ExtNode2 has nibbles [3, 4]. ExtNode1 branch has a leaf at position 4 (key3) and
an extension node ExtNode3 at position 5. ExtNode3 has only one nibble: 6.

Now we add delete key3 from the trie. ExtNode2 is now deleted from the trie, instead,
ExtNode1 appears with nibbles [3, 4, 5, 6] - ExtNode1 appears when ExtNode3 is lifted
from ExtNode2 branch for one level.

The terminology used for the modified extension node is:
ExtNode1 (nibbles [3, 4, 5, 6]) is named `long`.
ExtNode3 (ExtNode1 drifted into a branch of ExtNode2) is named `short` (only has one nibble: 6).
ExtNode2 (nibbles [3, 4]) is named `middle`.

Note that the branch rows above the leaf again contain the branch of `middle` extension node
and a placeholder branch (this extension node is actually deleted, but this way the constraints
for insert can be reused for delete operation, but not that as opposed to insert case
the placeholder branch is now in `C` proof).
We do not have `long` extension node and its branch stored anywhere
above the leaf. Instead, it is stored in `LONG_EXT_NODE_S` row (`LONG_EXT_NODE_C` is used
only for the second nibbles). We need to ensure that the hash of `long` extension node
is at `modified_node` position in the branch above `middle` rows in `S` proof.
`SHORT_EXT_NODE_S` rows contain `short` extension node. We need to ensure that
its hash is at `drifted_pos` in `middle` branch.

Note that `S` and `C` hashes (values in `c_main`) in the two `long` rows are the same. Likewise for
the two `short` rows. So the constraints like RLC and RLP are checked only for `S` rows (`c_main`
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
        inter_start_root: Column<Advice>,
        inter_final_root: Column<Advice>,
        position_cols: PositionCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        branch: BranchCols<F>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        keccak_table: KeccakTable,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        is_long: bool,
        check_zeros: bool,
    ) -> Self {
        let config = ExtensionNodeInsertedConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::from(1_u64));
        let c16 = Expression::Constant(F::from(16));
        let c16inv = Expression::Constant(F::from(16).invert().unwrap());
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
            is_long,
        );

        /*
        When we have an extension node in the first level of the account trie,
        its hash needs to be compared to the root of the trie.

        Note that existing extension node never appears in the first level (it can in `getProof`
        response) because the witness generator puts it after the leaf of the inserted extension
        node rows. So to check whether the existing extension node is in the first level, we need
        to check whether the inserted extension node is in the first level.
        */
        if is_long {
            meta.lookup_any(
                "Account first level (existing) extension node hash - compared to root",
                |meta| {
                    let q_enable = q_enable(meta);

                    let rot_into_branch = - LONG_EXT_NODE_S - 1 - ACCOUNT_LEAF_ROWS_NUM;

                    let not_first_level =
                        meta.query_advice(position_cols.not_first_level, Rotation(rot_into_branch));

                    let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                    let is_c_inserted = get_is_inserted_extension_node(
                        meta, c_main.rlp1, c_main.rlp2, rot_into_branch - BRANCH_ROWS_NUM + 1, true);
                    let root =
                        meta.query_advice(inter_start_root, Rotation::cur()) * is_c_inserted.clone()
                        + meta.query_advice(inter_final_root, Rotation::cur()) * (one.clone() - is_c_inserted);

                    let selector = q_enable * (one.clone() - not_first_level);

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
        }
        /*
        Note: else case (!is_long) is not needed here as the `short` extension node 
        needs to be checked to be the neighbour leaf in the branch (no comparison with trie root).
        */

        /*
        When extension node is in the first level of the storage trie, we need to check whether
        `hash(ext_node) = storage_trie_root`. We do this by checking whether
        `(ext_node_RLC, storage_trie_root_RLC)` is in the keccak table.

        Only check for the `before` row as this presents the extension node before the modification.
        The `after` row present the modified extension node which needs to be checked to correspond
        to the existing extension node that was modified due to inserted extension node.

        Note: extension node in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        if is_long {
            meta.lookup_any(
                "(Existing) extension node in first level of storage trie - hash compared to the storage root",
                |meta| {
                    let q_enable = q_enable(meta);

                    let rot_into_last_leaf_row = - LONG_EXT_NODE_S - 1;
                    let rot_into_branch_init = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;

                    // Check if there is an account above the existing extension node rows:
                    let is_account_leaf = meta.query_advice(
                        is_account_leaf_in_added_branch,
                        Rotation(rot_into_branch_init - 1),
                    ); 

                    let is_c_inserted = get_is_inserted_extension_node(
                        meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, true);

                    let acc = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                    let mut sc_hash = vec![];
                    // Note: storage root is always in `s_main.bytes`.
                    for column in s_main.bytes.iter() {
                        sc_hash.push(
                            meta.query_advice(*column, Rotation(rot_into_branch_init - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND))) * is_c_inserted.clone()
                            + meta.query_advice(*column, Rotation(rot_into_branch_init - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND))) * (one.clone() - is_c_inserted.clone())
                        );
                    }
                    let hash_rlc = bytes_expr_into_rlc(&sc_hash, power_of_randomness[0].clone());

                    let selector = q_enable * is_account_leaf;

                    let mut table_map = Vec::new();
                    let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                    table_map.push((selector.clone(), keccak_is_enabled));

                    let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                    table_map.push((selector.clone() * acc, keccak_input_rlc));

                    let ext_len =
                        meta.query_advice(s_main.rlp1, Rotation::cur()) - c192.clone() + one.clone();

                    let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                    table_map.push((selector.clone() * ext_len, keccak_input_len));

                    let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                    table_map.push((selector * hash_rlc, keccak_output_rlc));

                    table_map
                },
            );
        } 
        /*
        Note: else case (!is_long) is not needed here as the `short` extension node 
        needs to be checked to be the neighbour leaf in the branch (no comparison with trie root).
        */

        /*
        Check whether the extension node hash is in the parent branch.
        That means we check whether
        `(extension_node_RLC, node_hash_RLC)` is in the keccak table where `node` is a parent
        branch child at `modified_node` position.

        For `!is_long`, we rotate into the branch above the leaf. That means we check whether
        `short` extension node is at `drifted_pos` in the branch of `middle` extension node.

        For `is_long`, we go one level further up. That means we check whether `long` extension node
        is in `S` proof for `is_c_inserted` and in `C` proof for `1 - is_c_inserted`.

        Note that the constraints for `long` and `short` extension node being different only
        in the extension node nibbles are written separately.
        */
        meta.lookup_any("Extension node hash in parent branch", |meta| {
            let q_enable = q_enable(meta);

            let mut rot_into_last_leaf_row = - LONG_EXT_NODE_S - 1;
            if !is_long {
                rot_into_last_leaf_row = - SHORT_EXT_NODE_S - 1;
            }

            let rot_into_branch_init_storage = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;
            let rot_into_branch_init_account = rot_into_last_leaf_row - ACCOUNT_LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;

            let is_account_proof = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_last_leaf_row),
            );

            let is_ext_node_non_hashed =
                meta.query_advice(s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM], Rotation(-1));

            let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

            let is_c_inserted_ext_node_storage = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init_storage, true);
            let is_c_inserted_ext_node_account = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init_account, true);
             
            /*
            Note: Placeholder branch stores in `mod_node_hash_rlc` the hash of the drifted extension node.
            */

            // Rotation into a branch above the last branch:
            let mut rot_into_branch_storage = rot_into_branch_init_storage - 1 - EXTENSION_ROWS_NUM;
            let mut rot_into_branch_account = rot_into_branch_init_account - 1 - EXTENSION_ROWS_NUM;
            if !is_long {
                // Rotation into the last branch:
                rot_into_branch_storage = rot_into_branch_init_storage + 1;
                rot_into_branch_account = rot_into_branch_init_account + 1;
            }

            // If we are in an account proof, we check whether the branch above the inserted extension
            // rows is in first level.
            // If we are in a storage proof (storage proof in never in the first level), we check
            // whether there is an account leaf above the branch above the inserted extension rows.
            let not_first_level =
                is_account_proof.clone()
                * meta.query_advice(position_cols.not_first_level, Rotation(rot_into_branch_init_account))
                + (one.clone() - is_account_proof.clone())
                * (one.clone() - meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_branch_init_storage - 1)));

            /*
            Short extension node is in the branch above the leaf (at `drifted_pos`),
            while long extension node is in the branch one level above that
            (see rotation setting `rot_into_branch_storage` and `rot_into_branch_account` above).
            */

            let mod_node_hash_rlc_cur =
                is_account_proof.clone() *
                (meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_branch_account))
                * is_c_inserted_ext_node_account.clone()
                + meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_branch_account))
                * (one.clone() - is_c_inserted_ext_node_account.clone()))
                + (one.clone() - is_account_proof.clone()) *
                (meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_branch_storage))
                * is_c_inserted_ext_node_storage.clone()
                + meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_branch_storage))
                * (one.clone() - is_c_inserted_ext_node_storage));

            let selector = not_first_level
                * q_enable
                * (one.clone() - is_ext_node_non_hashed);

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
            table_map.push((selector * mod_node_hash_rlc_cur, keccak_output_rlc));

            table_map
        });

        meta.create_gate(
            "Extension node in parent branch (non-hashed extension node)",
            |meta| {
                let q_enable = q_enable(meta);
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());

                let mut rot_into_last_leaf_row = - LONG_EXT_NODE_S - 1;
                if !is_long{
                    rot_into_last_leaf_row = - SHORT_EXT_NODE_S - 1;
                }
                let rot_into_branch_init_storage = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;
                let rot_into_branch_init_account = rot_into_last_leaf_row - ACCOUNT_LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;

                let is_account_proof = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_last_leaf_row),
                );

                let is_ext_node_non_hashed =
                    meta.query_advice(s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM], Rotation(-1));

                let mut constraints = vec![];

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                let is_c_inserted_ext_node_storage = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init_storage, true);
                let is_c_inserted_ext_node_account = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init_account, true);

                // Rotation into a branch above the last branch:
                let mut rot_into_branch_storage = rot_into_branch_init_storage - 1 - EXTENSION_ROWS_NUM;
                let mut rot_into_branch_account = rot_into_branch_init_account - 1 - EXTENSION_ROWS_NUM;
                if !is_long {
                    // Rotation into the last branch:
                    rot_into_branch_storage = rot_into_branch_init_storage + 1;
                    rot_into_branch_account = rot_into_branch_init_account + 1;
                }

                let not_first_level =
                    is_account_proof.clone()
                    * meta.query_advice(position_cols.not_first_level, Rotation(rot_into_branch_init_account))
                    + (one.clone() - is_account_proof.clone())
                    * (one.clone() - meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_branch_init_storage - 1)));

                let mod_node_hash_rlc_cur =
                    is_account_proof.clone() *
                    (meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_branch_account))
                    * is_c_inserted_ext_node_account.clone()
                    + meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_branch_account))
                    * (one.clone() - is_c_inserted_ext_node_account.clone()))
                    + (one.clone() - is_account_proof.clone()) *
                    (meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_branch_storage))
                    * is_c_inserted_ext_node_storage.clone()
                    + meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_branch_storage))
                    * (one.clone() - is_c_inserted_ext_node_storage));

                /*
                When an extension node is not hashed, we do not check whether it is in a parent
                branch using a lookup (see above), instead we need to check whether the branch child
                at `modified_node` position is exactly the same as the extension node.
                */
                constraints.push((
                    "Non-hashed extension node in parent branch",
                    q_not_first
                        * q_enable
                        * not_first_level
                        * is_ext_node_non_hashed
                        * (mod_node_hash_rlc_cur - acc_c),
                ));

                constraints
            },
        );

        if !is_long {
            meta.create_gate(
                "Existing and drifted extension node differ only in nibbles",
                |meta| {
                    let q_enable = q_enable(meta);
                    let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());

                    let mut constraints = vec![];

                    let mut long_ext_branch = vec![];
                    let mut short_ext_branch = vec![];
                    for column in c_main.bytes.iter() {
                        long_ext_branch.push(meta.query_advice(*column, Rotation(-(SHORT_EXT_NODE_S - LONG_EXT_NODE_S))));
                        short_ext_branch.push(meta.query_advice(*column, Rotation::cur()));
                    }
                    let long_ext_branch_rlc = bytes_expr_into_rlc(&long_ext_branch, power_of_randomness[0].clone());
                    let short_ext_branch_rlc = bytes_expr_into_rlc(&short_ext_branch, power_of_randomness[0].clone());

                    /*
                    Existing and drifted extension node have the same `c_main.bytes` - same underlying branch.
                    */
                    constraints.push((
                        "Existing and drifted extension node have the same underlying branch",
                        q_not_first.clone()
                            * q_enable.clone()
                            * (short_ext_branch_rlc - long_ext_branch_rlc),
                    ));

                    /*
                    Note: otherwise the existing extension node (corrupted nibbles) might not lead
                    to the requested address (account proof) or storage key (storage proof).
                    */

                    let rot_into_last_leaf_row = - SHORT_EXT_NODE_S - 1;
                    let rot_into_branch_init_storage = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;
                    let rot_into_branch_init_account = rot_into_last_leaf_row - ACCOUNT_LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;
                    let rot_into_ext_node_storage = rot_into_last_leaf_row - LEAF_ROWS_NUM - 1;
                    let rot_into_ext_node_account = rot_into_last_leaf_row - ACCOUNT_LEAF_ROWS_NUM - 1;

                    let is_account_proof = meta.query_advice(
                        is_account_leaf_in_added_branch,
                        Rotation(rot_into_last_leaf_row),
                    );

                    let is_middle_longer_than_55 = meta.query_advice(
                        s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                        Rotation(rot_into_branch_init_account)) * is_account_proof.clone()
                        + meta.query_advice(
                        s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                        Rotation(rot_into_branch_init_storage)) * (one.clone() - is_account_proof.clone());
                    let is_middle_short =
                        get_is_extension_node_one_nibble(meta, s_main.bytes, rot_into_branch_init_account) * is_account_proof.clone()
                        + get_is_extension_node_one_nibble(meta, s_main.bytes, rot_into_branch_init_storage) * (one.clone() - is_account_proof.clone());
                    let is_middle_even_nibbles =
                        get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_into_branch_init_account) * is_account_proof.clone()
                        + get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_into_branch_init_storage) * (one.clone() - is_account_proof.clone());
                    let is_middle_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(
                        meta,s_main.bytes, rot_into_branch_init_account) * is_account_proof.clone()
                        + get_is_extension_node_long_odd_nibbles(
                        meta,s_main.bytes, rot_into_branch_init_storage) * (one.clone() - is_account_proof.clone());

                    let rot_selectors_long = -(SHORT_EXT_NODE_S - LONG_EXT_NODE_SELECTORS);
                    let rot_selectors_short = -(SHORT_EXT_NODE_S - SHORT_EXT_NODE_SELECTORS);

                    let is_long_longer_than_55 = meta.query_advice(
                        s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                        Rotation(rot_selectors_long),
                    );
                    // existing extension node cannot be short, otherwise no extension node could be inserted
                    let is_long_even_nibbles =
                        get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_selectors_long);
                    let is_before_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(
                        meta,
                        s_main.bytes,
                        rot_selectors_long,
                    );

                    let is_short_longer_than_55 = meta.query_advice(
                        s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                        Rotation(rot_selectors_short),
                    );
                    let is_short_short =
                        get_is_extension_node_one_nibble(meta, s_main.bytes, rot_selectors_short);
                    let is_short_even_nibbles =
                        get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_selectors_short);
                    let is_after_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(
                        meta,
                        s_main.bytes,
                        -(SHORT_EXT_NODE_S - SHORT_EXT_NODE_SELECTORS),
                    );

                    let middle_s_rlp2 =
                        meta.query_advice(s_main.rlp2, Rotation(rot_into_ext_node_account)) * is_account_proof.clone()
                        + meta.query_advice(s_main.rlp2, Rotation(rot_into_ext_node_storage)) * (one.clone() - is_account_proof.clone());
                    let middle_s_main0 =
                        meta.query_advice(s_main.bytes[0], Rotation(rot_into_ext_node_account)) * is_account_proof.clone()
                        + meta.query_advice(s_main.bytes[0], Rotation(rot_into_ext_node_storage)) * (one.clone() - is_account_proof.clone());
                    let long_s_rlp2 =
                        meta.query_advice(s_main.rlp2, Rotation(-(SHORT_EXT_NODE_S - LONG_EXT_NODE_S)));
                    let long_s_main0 =
                        meta.query_advice(s_main.bytes[0], Rotation(-(SHORT_EXT_NODE_S - LONG_EXT_NODE_S)));

                    let short_s_rlp2 =
                        meta.query_advice(s_main.rlp2, Rotation::cur());
                    let short_s_main0 =
                        meta.query_advice(s_main.bytes[0], Rotation::cur());

                    let c2 = Expression::Constant(F::from(2));

                    let middle_nibbles_num =
                        (one.clone() - is_middle_longer_than_55.clone()) *
                        (is_middle_even_nibbles.clone() * (middle_s_rlp2.clone() - c128.clone() - one.clone()) * c2.clone()
                        + (one.clone() - is_middle_even_nibbles.clone())
                        * (((middle_s_rlp2.clone() - c128.clone()) * c2.clone() - one.clone()) * (one.clone() - is_middle_short.clone())
                        + is_middle_short.clone()))
                        + is_middle_longer_than_55.clone()
                        * (is_middle_even_nibbles.clone() * (middle_s_rlp2.clone() - c128.clone() - one.clone()) * c2.clone()
                        + (one.clone() - is_middle_even_nibbles.clone())
                        * (((middle_s_rlp2.clone() - c128.clone()) * c2.clone() - one.clone()) * (one.clone() - is_middle_short.clone())
                        + is_middle_short.clone()));

                    // Note: long extension node cannot be short (having only one nibble)
                    let long_nibbles_num =
                        (one.clone() - is_long_longer_than_55.clone())
                        * (is_long_even_nibbles.clone() * (long_s_rlp2.clone() - c128.clone() - one.clone()) * c2.clone()
                        + (one.clone() - is_long_even_nibbles.clone()) * ((long_s_rlp2.clone() - c128.clone()) * c2.clone() - one.clone()))
                        + is_long_longer_than_55
                        * (is_long_even_nibbles.clone() * (long_s_main0.clone() - c128.clone() - one.clone()) * c2.clone()
                        + (one.clone() - is_long_even_nibbles.clone()) * ((long_s_main0.clone() - c128.clone()) * c2.clone() - one.clone()));

                    let short_nibbles_num =
                        (one.clone() - is_short_longer_than_55.clone())
                        * (is_short_even_nibbles.clone() * (short_s_rlp2.clone() - c128.clone() - one.clone()) * c2.clone()
                        + (one.clone() - is_short_even_nibbles.clone())
                        * (((short_s_rlp2.clone() - c128.clone()) * c2.clone() - one.clone()) * (one.clone() - is_short_short.clone())
                        + is_short_short.clone()))
                        + is_short_longer_than_55.clone()
                        * (is_short_even_nibbles.clone() * (short_s_rlp2.clone() - c128.clone() - one.clone()) * c2.clone()
                        + (one.clone() - is_short_even_nibbles.clone())
                        * (((short_s_rlp2.clone() - c128.clone()) * c2.clone() - one.clone()) * (one.clone() - is_short_short.clone())
                        + is_short_short.clone()));
 
                    constraints.push((
                        "The number of nibbles of the long extension node corresponds to the nibbles in the middle and short extension node",
                        q_not_first.clone()
                            * q_enable.clone()
                            * (long_nibbles_num - middle_nibbles_num - short_nibbles_num - one.clone()),
                            // -1 because one nibble is used for the position of the extension node in the branch
                    ));

                    // `drifted_pos` is stored in branch children
                    let drifted_pos =
                        meta.query_advice(branch.drifted_pos, Rotation(rot_into_branch_init_account + 1))
                        * is_account_proof.clone() 
                        + meta.query_advice(branch.drifted_pos, Rotation(rot_into_branch_init_storage + 1))
                        * (one.clone() - is_account_proof.clone()); 

                    // 0 if `is_before_even_nibbles`:
                    // Note: before cannot be short because otherwise no extension node could be inserted
                    let mut long_nibbles_rlc =
                        (long_s_main0 - c16.clone()) * c16.clone()
                        * (one.clone() - is_long_even_nibbles.clone());

                    let first_nibble =
                        (short_s_main0.clone() - c16.clone()) * (one.clone() - is_short_short.clone())
                        + (short_s_rlp2.clone() - c16.clone()) * is_short_short.clone();
                    // 0 if `is_after_even_nibbles`:
                    let mut short_nibbles_rlc =
                        (first_nibble.clone() * c16.clone() * (one.clone() - is_middle_even_nibbles.clone()) // `1 - is_even_nibbles` because of `drifted_pos`
                        + first_nibble * is_middle_even_nibbles.clone())
                        * (one.clone() - is_short_even_nibbles.clone());

                    // 0 if `is_even_nibbles`:
                    let mut middle_nibbles_rlc =
                        ((middle_s_main0 - c16.clone()) * c16.clone() * (one.clone() - is_middle_short.clone()) + (middle_s_rlp2.clone() - c16.clone()) * c16.clone() * is_middle_short.clone())
                        * (one.clone() - is_middle_even_nibbles.clone());

                    let mut mult = Expression::Constant(F::one());
                    for ind in 0..HASH_WIDTH-1 {
                        let long_s = meta.query_advice(s_main.bytes[1+ind], Rotation(-(SHORT_EXT_NODE_S - LONG_EXT_NODE_S)));
                        let long_second_nibble = meta.query_advice(s_main.bytes[ind], Rotation(-(SHORT_EXT_NODE_S - LONG_EXT_NODE_C)));
                        let long_first_nibble = (long_s.clone() - long_second_nibble.clone()) * c16inv.clone();
    
                        let middle_s =
                            meta.query_advice(s_main.bytes[1+ind], Rotation(rot_into_ext_node_account))
                            * is_account_proof.clone()
                            + meta.query_advice(s_main.bytes[1+ind], Rotation(rot_into_ext_node_storage))
                            * (one.clone() - is_account_proof.clone());
                        let middle_second_nibble =
                            meta.query_advice(s_main.bytes[ind], Rotation(rot_into_ext_node_account + 1))
                            * is_account_proof.clone()
                            + meta.query_advice(s_main.bytes[ind], Rotation(rot_into_ext_node_storage + 1))
                            * (one.clone() - is_account_proof.clone());
                        let middle_first_nibble = (middle_s.clone() - middle_second_nibble.clone()) * c16inv.clone();

                        let short_s = meta.query_advice(s_main.bytes[1+ind], Rotation::cur());
                        let short_second_nibble = meta.query_advice(s_main.bytes[ind], Rotation::next());
                        let short_first_nibble = (short_s.clone() - short_second_nibble.clone()) * c16inv.clone();
                        
                        long_nibbles_rlc = long_nibbles_rlc
                            + (long_first_nibble.clone() * c16.clone() + long_second_nibble.clone()) * mult.clone() * is_long_even_nibbles.clone()
                            + (long_first_nibble + long_second_nibble * c16.clone() * power_of_randomness[0].clone()) * mult.clone() * (one.clone() - is_long_even_nibbles.clone());

                        middle_nibbles_rlc = middle_nibbles_rlc
                            + (middle_first_nibble.clone() * c16.clone() + middle_second_nibble.clone()) * mult.clone() * is_middle_even_nibbles.clone()
                            + (middle_first_nibble + middle_second_nibble * c16.clone() * power_of_randomness[0].clone()) * mult.clone() * (one.clone() - is_middle_even_nibbles.clone()); 

                        // `short_nibbles_rlc` computation depends on whether `middle_nibbles_rlc` has even or odd nibbles
                        short_nibbles_rlc = short_nibbles_rlc
                            + (short_first_nibble.clone() * c16.clone() + short_second_nibble.clone()) * mult.clone()
                            * (is_short_even_nibbles.clone() * (one.clone() - is_middle_even_nibbles.clone()) + (one.clone() - is_short_even_nibbles.clone()) * is_middle_even_nibbles.clone())
                            + (short_first_nibble.clone() + short_second_nibble.clone() * c16.clone() * power_of_randomness[0].clone()) * mult.clone()
                            * ((is_short_even_nibbles.clone() * is_middle_even_nibbles.clone() + (one.clone() - is_short_even_nibbles.clone()) * (one.clone() - is_middle_even_nibbles.clone())));

                        mult = mult * power_of_randomness[0].clone();
                    } 

                    let mult_after = meta.query_advice(
                        accs.acc_c.mult,
                        Rotation(rot_into_ext_node_account)) * is_account_proof.clone()
                        + meta.query_advice(
                        accs.acc_c.mult,
                        Rotation(rot_into_ext_node_storage)) * (one.clone() - is_account_proof.clone());

                    middle_nibbles_rlc = middle_nibbles_rlc
                        + (drifted_pos.clone() * c16.clone() + short_nibbles_rlc.clone()) * mult_after.clone() * is_middle_even_nibbles.clone()
                        + (drifted_pos.clone() + short_nibbles_rlc.clone() * power_of_randomness[0].clone()) * mult_after.clone() * (one.clone() - is_middle_even_nibbles.clone());

                    constraints.push((
                        "Nibbles in before are the same as nibbles in inserted + after",
                        q_not_first
                            * q_enable
                            * (long_nibbles_rlc - middle_nibbles_rlc)
                    ));

                    constraints
                },
            );
        }

        /*
        To know each nibble individually (they come in pairs as bytes), the second nibbles
        are in `C` row, from which we can compute the first nibbles.

        Correspondence between nibbles in C and bytes in S for
        regular extension nodes is ensured in `extension_node_key.rs`.
        */
        meta.create_gate("Existing node: first nibble / second nibble & s_main bytes are 0 when short extension node", |meta| {
            let q_enable = q_enable(meta);
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());

            let mut constraints = vec![];

            for ind in 0..HASH_WIDTH-1 {
                let s = meta.query_advice(s_main.bytes[1+ind], Rotation::cur());
                let second_nibble = meta.query_advice(s_main.bytes[ind], Rotation::next());
                let first_nibble = (s.clone() - second_nibble.clone()) * c16inv.clone();
                /*
                Note that first_nibble and second_nibble need to be between 0 and 15 - this
                is checked in a lookup below.
                */
                constraints.push((
                    "First_nibble second_nibble (existing extension node)",
                    q_enable.clone()
                        * q_not_first.clone()
                        * (s - first_nibble.clone() * c16.clone() - second_nibble.clone())
                ));
            }

            let is_ext_short_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_short_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM],
                Rotation(-1),
            );

            /*
            We need to ensure `s_main.bytes` are all 0 when short - the only nibble is in `s_main.rlp2`.
            For long version, the constraints to have 0s after nibbles end in `s_main.bytes` are
            implemented using `key_len_lookup`.
            */
            for ind in 0..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                constraints.push((
                    "s_main.bytes[i] = 0 for short",
                        q_enable.clone()
                        * q_not_first.clone()
                        * (is_ext_short_c1.clone() + is_ext_short_c16.clone())
                        * s,
                ));
            }
            
            constraints
        });

        for ind in 0..HASH_WIDTH - 1 {
            meta.lookup_any("(Existing) extension node second_nibble", |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let second_nibble = meta.query_advice(s_main.bytes[ind], Rotation::next());

                constraints.push((
                    Expression::Constant(F::from(FixedTableTag::Range16 as u64)),
                    meta.query_fixed(fixed_table[0], Rotation::cur()),
                ));
                constraints.push((
                    q_enable * second_nibble,
                    meta.query_fixed(fixed_table[1], Rotation::cur()),
                ));

                constraints
            });
        }

        check_intermediate_mult(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            accs,
            -1,
            fixed_table,
            power_of_randomness[1].clone(),
        );

        let sel_branch_non_hashed = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);

            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            // c_rlp2 = 160 when branch is hashed (longer than 31) and c_rlp2 = 0 otherwise
            let is_branch_hashed = c_rlp2 * c160_inv.clone();

            q_enable * (one.clone() - is_branch_hashed)
        };

        let sel_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);

            let is_ext_long_even_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_long = is_ext_long_even_c16
                + is_ext_long_even_c1
                + is_ext_long_odd_c16
                + is_ext_long_odd_c1;

            q_enable * is_long
        };

        /*
        `s_main.bytes[i] = 0` after last extension node nibble.

        Note that for a short version (only one nibble), all
        `s_main.bytes` need to be 0 (the only nibble is in `s_main.rlp2`) - this is checked
        separately.
        */
        if check_zeros {
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
        There are 0s after non-hashed branch ends in `c_main.bytes`.
        */
        if check_zeros {
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_branch_non_hashed,
                    ind,
                    c_main.bytes[0],
                    c_main.bytes[ind],
                    192,
                    fixed_table,
                )
            }
        }

        /*
        Note: range_lookups for regular extension nodes are in `extension_node_key.rs`, but
        we do not have `_key.rs` for the inserted extension node.
        */
        range_lookups(
            meta,
            q_enable.clone(),
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable.clone(),
            c_main.bytes.to_vec(),
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
            let len_full_bytes: usize; // how many pairs of nibbles
            if row.get_byte(1) <= 32 {
                // key length is 1
                len_full_bytes = 0;
                len = 2 // [length byte, key]
            } else if row.get_byte(0) < 248 {
                len_full_bytes = (row.get_byte(1) - 128) as usize - 1;
                len = len_full_bytes + 1 + 2; // +1 for the first position which might contain 0 or 1 nibble
            } else {
                len_full_bytes = (row.get_byte(1) - 128) as usize - 1;
                len = len_full_bytes + 1 + 3; // +1 for the first position which might contain 0 or 1 nibble
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

            let mut nibbles_rlc_mult = F::one();
            for ind in 0..len_full_bytes {
                nibbles_rlc_mult *= mpt_config.randomness;
            }

            // We don't need to store `pv.acc_mult_c`, so we can store `nibbles_rlc_mult` using `acc_mult_c`.
            mpt_config
                .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, nibbles_rlc_mult, offset)
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
