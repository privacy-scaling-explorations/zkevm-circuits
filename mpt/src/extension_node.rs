use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Instance, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, get_bool_constraint, hash_expr_into_rlc},
    param::{
        HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
        IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
        KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeConfig {}

pub(crate) struct ExtensionNodeChip<F> {
    config: ExtensionNodeConfig,
    _marker: PhantomData<F>,
}

/*
Let's say we have branch1 and branch2 below it.

branch1 S row 0 || branch1 C row 0
...
branch1 S row 15 || branch1 C row 15

branch2 S row 0 || branch2 C row 0
...
branch2 S row 15 || branch2 C row 15

Hash of branch2 S is in one of the branch1 rows (in S columns).
Hash of branch2 C is in one of the branch1 rows (in C columns).

In what follows, we write branch without S and C - it is the same for both cases.

Key key1 determines the position of branch2 hash in branch1 (0-15).
To check this, branch2 RLC (over all RLP bytes - all 1+16 rows, 1 is for branch init row)
is checked to have a hash in branch1, at modified_node index
(modified_node depends on key key1).

However, with extension node it's a bit different.

branch1 S row 0 || branch1 C row 0
...
branch1 S row 15 || branch1 C row 15
extension1 S
extension1 C

branch2 S row 0 || branch2 C row 0
...
branch2 S row 15 || branch2 C row 15
extension2 S
extension2 C

There are additional rows immediately after branch 16 rows - one row for
extension node S and one row for extension node C. These rows are empty when
we have a regular branch.

Let's say branch2 is extension node. In this case, extension2 row contains:
  - key bytes that present the extension
  - hash of branch2

---
Example 1:

Key extension of length 2:
[228, 130, 0,          149,        160, 114,                    253,                     150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
[rlp, rlp, key byte 1, key byte 2, rlp, hash of branch2 byte 0, hash of branch2 byte 1, ...]
[0, 149] presents key extension:
  - 0 because it's even length (in branch it would be 16, see terminator)
  - 149 = 9*16 + 5
Key extension is [9, 5].

Two constraints are needed:
  - the hash of extension node (extension node RLC is needed) needs to be
    checked whether it's in branch1
  - the hash of branch2 is in extension node.

Also, it needs to be checked that key extension corresponds to key1 (not in this chip).

---
Example 2:

Key extension of length 1:
[226, 16,        160,172,105,12...
[rlp, key byte1, ...
[16] presents key extension:
  - 16 = 0 + 16
Key extension is [0].

*/

impl<F: FieldExt> ExtensionNodeChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        root: Column<Instance>,
        not_first_level: Column<Advice>,
        q_not_first: Column<Fixed>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        is_branch_init: Column<Advice>, /* to avoid ConstraintPoisened and failed lookups (when
                                         * rotation lands < 0) */
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_c: Column<Advice>,
        acc_mult_c: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        mod_node_hash_rlc: Column<Advice>,
        r_table: Vec<Expression<F>>,
        is_s: bool,
        acc_r: F,
    ) -> ExtensionNodeConfig {
        let config = ExtensionNodeConfig {};
        let one = Expression::Constant(F::from(1_u64));
        let c128 = Expression::Constant(F::from(128));
        let c226 = Expression::Constant(F::from(226));
        let mut rot_into_branch_init = -17;
        if !is_s {
            rot_into_branch_init = -18;
        }

        // Note that is_extension_node is not explicitly checked (for example, what if
        // the attacker sets is_extension_node = 1 for a regular branch or the other way
        // around), however, this check is done implicitly with key RLC
        // constraints (the final key RLC will fail if is_extension_node is set
        // to 1 for a regular branch or if is_extension_node is set to 0 for an
        // extension node).
        meta.create_gate("Extension node selectors", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // NOTE: even and odd is for number of nibbles that are compactly encoded.

            // To reduce the expression degree, we pack together multiple information.
            let is_ext_short_c16 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_short_c1 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );

            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());

            constraints.push((
                "bool check is_ext_short_c16",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_short_c16.clone(),
                ),
            ));
            constraints.push((
                "bool check is_ext_short_c1",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_short_c1.clone(),
                ),
            ));
            constraints.push((
                "bool check is_ext_long_even_c16",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_long_even_c16.clone(),
                ),
            ));
            constraints.push((
                "bool check is_ext_long_even_c1",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_long_even_c1.clone(),
                ),
            ));
            constraints.push((
                "bool check is_ext_long_odd_c16",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_long_odd_c16.clone(),
                ),
            ));
            constraints.push((
                "bool check is_ext_long_odd_c1",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_long_odd_c1.clone(),
                ),
            ));

            // At most one of the six selectors above can be enabled. If sum is 0, it is
            // a regular branch. If sum is 1, it is an extension node.
            constraints.push((
                "bool check extension node selectors sum",
                get_bool_constraint(
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone()),
                    is_ext_short_c16.clone()
                        + is_ext_short_c1.clone()
                        + is_ext_long_even_c16.clone()
                        + is_ext_long_even_c1.clone()
                        + is_ext_long_odd_c16.clone()
                        + is_ext_long_odd_c1.clone(),
                ),
            ));

            // is_branch_c16 and is_branch_c1 correspond to the six extension selectors.
            let is_branch_c16 = meta.query_advice(
                s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_branch_c1 = meta.query_advice(
                s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let mut constrain_sel = |branch_sel: Expression<F>, ext_sel: Expression<F>| {
                constraints.push((
                    "branch c16/c1 selector - extension c16/c1 selector",
                    q_not_first.clone()
                        * q_enable.clone()
                        * (one.clone() - is_branch_init_prev.clone())
                        * ext_sel.clone()
                        * (branch_sel - ext_sel),
                ));
            };

            constrain_sel(is_branch_c16.clone(), is_ext_short_c16.clone());
            constrain_sel(is_branch_c1.clone(), is_ext_short_c1.clone());
            constrain_sel(is_branch_c16.clone(), is_ext_long_even_c16.clone());
            constrain_sel(is_branch_c1.clone(), is_ext_long_even_c1.clone());
            constrain_sel(is_branch_c16.clone(), is_ext_long_odd_c16.clone());
            constrain_sel(is_branch_c1.clone(), is_ext_long_odd_c1.clone());

            /*
            If key_len = 1 (is_short = 1, is_long = 0)
            [226,16,160,172,105,12...
            there is no byte specifying key length, but in this case the first byte is 226.
            So, when s_rlp1 = 226, we need to ensure is_key_odd = 1, is_key_even = 0
            (is_key_even = 0 can be omitted because of the constraints above).

            If key_len > 1 (is_short = 0, is_long = 1)
            [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
            the second byte specifies the key_len (we need to subract 128 to get it).
            */

            // In C we have nibbles, we check below only for S.
            if is_s {
                let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
                let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());

                // This prevents setting to short when it's not short (s_rlp1 > 226 in that
                // case):
                constraints.push((
                    "short implies s_rlp1 = 226",
                    q_not_first.clone()
                        * q_enable.clone()
                        * (is_ext_short_c16.clone() + is_ext_short_c1.clone())
                        * (s_rlp1 - c226),
                ));

                // This prevents setting to even when it's not even,
                // because when it's not even s_advices0 != 0 (hexToCompact adds 16).
                constraints.push((
                    "long & even implies s_advices0 = 0",
                    q_not_first.clone()
                        * q_enable.clone()
                        * (is_ext_long_even_c16.clone() + is_ext_long_even_c1.clone())
                        * s_advices0,
                ));
            }

            constraints
        });

        // Note: acc_mult is checked in extension_node_key.

        // Check whether branch hash is in extension node row.
        meta.lookup_any("extension_node branch hash in extension row", |meta| {
            let q_enable = q_enable(meta);
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());

            let mut acc = meta.query_advice(acc_s, Rotation(-1));
            let mut mult = meta.query_advice(acc_mult_s, Rotation(-1));
            if !is_s {
                acc = meta.query_advice(acc_c, Rotation(-2));
                mult = meta.query_advice(acc_mult_c, Rotation(-2));
            }
            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];
            constraints.push((
                q_not_first.clone()
                    * q_enable.clone()
                    * (one.clone() - is_branch_init_prev.clone())
                    * branch_acc, // TODO: replace with acc once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            let mut sc_hash = vec![];
            // Note: extension node has branch hash always in c_advices.
            for column in c_advices.iter() {
                sc_hash.push(meta.query_advice(*column, Rotation::cur()));
            }
            let hash_rlc = hash_expr_into_rlc(&sc_hash, acc_r);
            constraints.push((
                q_not_first.clone()
                    * q_enable.clone()
                    * (one.clone() - is_branch_init_prev)
                    * hash_rlc.clone(),
                meta.query_fixed(keccak_table[1], Rotation::cur()),
            ));

            constraints
        });

        // Check whether RLC is properly computed.
        meta.create_gate("Extension node RLC", |meta| {
            let mut constraints = vec![];
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let q_enable = q_enable(meta);
            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());

            let mut rot = 0;
            if !is_s {
                rot = -1;
            }

            // s_rlp1, s_rlp2, s_advices need to be the same in both extension rows.
            // However, to make space for nibble witnesses, we put nibbles in
            // extension row C s_advices. So we use s_advices from S row.

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation(rot));
            let mut rlc = s_rlp1;
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation(rot));
            rlc = rlc + s_rlp2 * r_table[0].clone();

            let s_advices_rlc = compute_rlc(
                meta,
                s_advices.to_vec(),
                1,
                one.clone(),
                rot,
                r_table.clone(),
            );
            rlc = rlc + s_advices_rlc;

            let acc_s = meta.query_advice(acc_s, Rotation(rot));
            constraints.push((
                "acc_s",
                q_not_first.clone()
                    * q_enable.clone()
                    * (one.clone() - is_branch_init_prev.clone())
                    * (rlc - acc_s.clone()),
            ));

            // We use rotation 0 in both cases from now on:
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            let c160 = Expression::Constant(F::from(160_u64));
            constraints.push((
                "c_rlp2",
                q_not_first.clone() * q_enable.clone() * (c_rlp2.clone() - c160),
            ));

            let acc_mult_s = meta.query_advice(acc_mult_s, Rotation::cur());
            rlc = acc_s + c_rlp2 * acc_mult_s.clone();

            let c_advices_rlc = compute_rlc(meta, c_advices.to_vec(), 0, acc_mult_s, 0, r_table);
            rlc = rlc + c_advices_rlc;

            let acc_c = meta.query_advice(acc_c, Rotation::cur());
            constraints.push((
                "acc_c",
                q_not_first
                    * q_enable
                    * (one.clone() - is_branch_init_prev.clone())
                    * (rlc - acc_c),
            ));

            constraints
        });

        // Correspondence between nibbles in C and bytes in S is checked in
        // extension_node_key.

        // TODO: prepare test
        meta.create_gate(
            "account first level extension node hash - compared to root",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let mut sc_hash = vec![];
                // Note: extension node has branch hash always in c_advices.
                for column in c_advices.iter() {
                    sc_hash.push(meta.query_advice(*column, Rotation::cur()));
                }
                let hash_rlc = hash_expr_into_rlc(&sc_hash, acc_r);
                let root = meta.query_instance(root, Rotation::cur());

                let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());
                constraints.push((
                    "first level extension node",
                    q_not_first
                        * q_enable.clone()
                        * (one.clone() - not_first_level)
                        * (one.clone() - is_branch_init_prev.clone()) // to prevent PoisonedConstraint
                        * (hash_rlc - root),
                ));

                constraints
            },
        );

        // Check whether extension node hash is in parent branch.
        // Don't check if it's first storage level (see storage_root_in_account_leaf).
        meta.lookup_any("extension_node extension in parent branch", |meta| {
            let q_enable = q_enable(meta);
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            let is_account_leaf_storage_codehash_c = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_branch_init - 1),
            );

            // When placeholder extension, we don't check its hash in a parent.
            let mut is_branch_placeholder = s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET];
            if !is_s {
                is_branch_placeholder = s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET];
            }
            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_branch_init));

            let mut constraints = vec![];

            let acc_c = meta.query_advice(acc_c, Rotation::cur());
            constraints.push((
                not_first_level.clone()
                    * q_enable.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_c.clone())
                    * (one.clone() - is_branch_placeholder.clone())
                    * acc_c,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            // Any rotation that lands into branch can be used instead of -21.
            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation(-21));
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                not_first_level.clone()
                    * q_enable.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_c.clone())
                    * (one.clone() - is_branch_placeholder.clone())
                    * mod_node_hash_rlc_cur,
                keccak_table_i,
            ));

            constraints
        });

        config
    }

    pub fn construct(config: ExtensionNodeConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for ExtensionNodeChip<F> {
    type Config = ExtensionNodeConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
