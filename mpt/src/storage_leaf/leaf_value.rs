use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation, circuit::Region,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{get_bool_constraint, key_len_lookup, range_lookups},
    mpt::{FixedTableTag, MPTConfig, ProofVariables},
    param::{BRANCH_ROWS_NUM, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, HASH_WIDTH}, columns::{MainCols, AccumulatorCols, DenoteCols}, witness_row::{MptWitnessRow, MptWitnessRowType},
};

/*
A storage leaf occupies 5 rows.
Contrary as in the branch rows, the `S` and `C` leaves are not positioned parallel to each other.
The rows are the following:
LEAF_KEY_S
LEAF_VALUE_S
LEAF_KEY_C
LEAF_VALUE_C
LEAF_DRIFTED

An example of leaf rows:
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]

In the above example the value has been changed from 1 (`LEAF_VALUE_S`) to 17 (`LEAF_VALUE_C`).

In the example below the value in `LEAF_VALUE_C` takes more than 1 byte: `[187 239 170 ...]`
This has two consequences:
 - Two additional RLP bytes: `[161 160]` where `33 = 161 - 128` means there are `31` bytes behind `161`,
   `32 = 160 - 128` means there are `30` bytes behind `160`.
 - `LEAF_KEY_S` starts with `248` because the leaf has more than 55 bytes, `1 = 248 - 247` means
   there is 1 byte after `248` which specifies the length - the length is `67`. We can see that
   that the leaf key is shifted by 1 position compared to the example above.

For this reason we need to distinguish two cases: 1 byte in leaf value, more than 1 byte in leaf value.
These two cases are denoted by `is_short` and `is_long`. There are two other cases we need to
distinguish: `last_level` when the leaf is in the last level and has no nibbles, `one_nibble` when
the leaf has only one nibble.

`is_long`:
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[161 160 187 239 170 18 88 1 56 188 38 60 149 117 120 38 223 78 36 235 129 201 170 170 170 170 170 170 170 170 170 170 170 170 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]

`last_level`
[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]

`one_nibble`:
[194 48 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[194 48 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]

`s_mod_node_rlc` (`flag1`) and `c_mod_node_rlc` (`flag2`) columns store the information of what
kind of case we have:
 `flag1: 1, flag2: 0`: `is_long`
 `flag1: 0, flag2: 1`: `is_short`
 `flag1: 1, flag2: 1`: `last_level`
 `flag1: 0, flag0: 1`: `one_nibble`

The constraints in `leaf_value.rs` apply to `LEAF_VALUE_S` and `LEAF_VALUE_C` rows.
The constraints ensure the hash of a storage leaf is in a parent branch and that the RLP of the leaf is correct.
*/

#[derive(Clone, Debug)]
pub(crate) struct LeafValueConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafValueConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_leaf_value: Column<Advice>,
        s_main: MainCols<F>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        /*
        - key_rlc_mult (accs.key.mult) to store key_rlc from previous row (to enable lookup)
        - mult_diff to store leaf value S RLC from two rows above (to enable lookup)
        TODO: check whether some other column can be used instead of mult_diff
        */
        accs: AccumulatorCols<F>,
        denoter: DenoteCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        is_branch_placeholder: Column<Advice>,
        is_s: bool,
        acc_r: F,
        fixed_table: [Column<Fixed>; 3],
    ) -> Self {
        let config = LeafValueConfig { _marker: PhantomData };

        /*
        A rotation into any branch child is ok as `s_mod_node_hash_rlc` and `c_mod_node_hash_rlc` are the same
        in all branch children.
        */
        let rot = -6;
        let mut rot_into_init = -20;
        let mut rot_into_account = -2;
        if !is_s {
            rot_into_init = -22;
            rot_into_account = -4;
        }
        let one = Expression::Constant(F::one());

        /*
        We need the RLC of the whole leaf for a lookup that ensures the leaf is in the parent branch.
        We need the leaf value RLC for external lookups that ensure the value has been set correctly.
        */
        meta.create_gate("Leaf & leaf value RLC", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * is_leaf;

            let mut constraints = vec![];

            let c128 = Expression::Constant(F::from(128));
            let c192 = Expression::Constant(F::from(192));
            let is_long = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let is_short = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::prev());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::prev());
            let last_level = flag1.clone() * flag2.clone();
            let is_leaf_long = flag1.clone() * (one.clone() - flag2.clone());
            let is_leaf_short = (one.clone() - flag1.clone()) * flag2.clone();
            let one_nibble = (one.clone() - flag1.clone()) * (one.clone() - flag2.clone());

            let s_rlp1_prev = meta.query_advice(s_main.rlp1, Rotation::prev());
            let s_rlp1_cur = meta.query_advice(s_main.rlp1, Rotation::cur());

            /*
            `is_short` means value has only one byte and consequently, the RLP of
            the value is only this byte itself. If there are more bytes, the value is
            equipped with two RLP meta bytes, like 161 160 if there is a
            value of length 32 (the first RLP byte means 33 bytes after it, the second
            RLP byte means 32 bytes after it).

            `is_short` example:
            `[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]`

            `is_long` example:
            `[161 160 187 239 170 18 88 1 56 188 38 60 149 117 120 38 223 78 36 235 129 201 170 170 170 170 170 170 170 170 170 170 170 170 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]`

            We need to ensure `is_long` and `is_short` are booleans and that `is_long + is_short = 1`.
            */
            constraints.push((
                "is_long is boolean",
                get_bool_constraint(q_enable.clone(), is_long.clone()),
            ));

            constraints.push((
                "is_short is boolean",
                get_bool_constraint(q_enable.clone(), is_long.clone()),
            ));

            constraints.push((
                "is_long + is_short = 1",
                q_enable.clone() * (is_long.clone() + is_short.clone() - one.clone()),
            ));

            let leaf_rlc_prev = meta.query_advice(accs.acc_s.rlc, Rotation::prev());
            let leaf_mult_prev = meta.query_advice(accs.acc_s.mult, Rotation::prev());
            let s_rlp2_prev = meta.query_advice(s_main.rlp2, Rotation::prev());
            let s_rlp2_cur = meta.query_advice(s_main.rlp2, Rotation::cur());

            let mut value_rlc_long = Expression::Constant(F::zero());
            let mut mult_long = F::one();
            for col in s_main.bytes.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                value_rlc_long = value_rlc_long + s * mult_long.clone();
                mult_long = mult_long * acc_r;
            }

            let leaf_value_rlc =
                value_rlc_long.clone() * is_long.clone() + s_rlp1_cur.clone() * is_short.clone();

            let leaf_rlc_long = leaf_rlc_prev.clone()
                + s_rlp1_cur.clone() * leaf_mult_prev.clone()
                + s_rlp2_cur.clone() * leaf_mult_prev.clone() * acc_r.clone()
                + value_rlc_long.clone() * leaf_mult_prev.clone() * acc_r.clone() * acc_r;
            let leaf_rlc = leaf_rlc_long * is_long.clone()
                + (leaf_rlc_prev + s_rlp1_cur.clone() * leaf_mult_prev) * is_short.clone();

            let acc_s = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
            let acc_c_cur = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

            /*
            We need to ensure that the stored leaf RLC is the same as the computed one.
            */
            constraints.push(("Leaf RLC", q_enable.clone() * (acc_s - leaf_rlc)));

            /*
            We need to ensure that the stored leaf value RLC is the same as the computed one.
            */
            constraints.push((
                "Leaf value RLC",
                q_enable.clone() * (acc_c_cur - leaf_value_rlc),
            ));
 
            if !is_s {
                let key_c_rlc_from_prev = meta.query_advice(accs.key.rlc, Rotation(-1));
                let key_c_rlc_from_cur = meta.query_advice(accs.key.mult, Rotation::cur());
                let leaf_value_s_rlc_from_prev = meta.query_advice(accs.acc_c.rlc, Rotation(-2));
                let leaf_value_s_rlc_from_cur = meta.query_advice(accs.mult_diff, Rotation::cur());
                
                /*
                To enable external lookups we need to have the following information in the same row:
                 - key RLC:                       we copy it to `sel1` column from the leaf key C row
                 - previous (`S`) leaf value RLC: we copy it to `sel2` column from the leaf value `S` row
                 - current (`C`) leaf value RLC:  stored in `acc_c` column
                */
                constraints.push((
                    "Leaf key C RLC properly copied",
                    q_enable.clone() * (key_c_rlc_from_prev - key_c_rlc_from_cur),
                ));

                constraints.push((
                    "Leaf value S RLC properly copied",
                    q_enable.clone() * (leaf_value_s_rlc_from_prev - leaf_value_s_rlc_from_cur),
                ));
            }
 
            let mut sel = meta.query_advice(denoter.sel1, Rotation(rot));
            if !is_s {
                sel = meta.query_advice(denoter.sel2, Rotation(rot));
            }
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            /*
            `sel` column in branch children rows determines whether the `modified_node` is empty child.
            For example when adding a new storage leaf to the trie, we have an empty child in `S` proof
            and non-empty in `C` proof. 
            When there is an empty child, we have a placeholder leaf under the last branch.

            If `sel = 1` which means an empty child, we need to ensure that the value is set to 0
            in the placeholder leaf.

            Note: For a leaf without a branch (means it is in the first level of the trie)
            the constraint is in `storage_root_in_account_leaf.rs`.
            */
            constraints.push((
                "Placeholder leaf (no value set) needs to have value = 0 (s_rlp1)",
                q_enable.clone()
                    * sel.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * s_rlp1_cur.clone(),
            ));

            constraints.push((
                "Placeholder leaf (no value set) needs to have value = 0 (s_rlp2)",
                q_enable.clone()
                    * sel.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * s_rlp2_cur.clone(),
            ));

            for col in s_main.bytes.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                constraints.push((
                    "Placeholder leaf (no value set) needs to have value = 0",
                    q_enable.clone()
                        * sel.clone()
                        * (one.clone() - is_leaf_without_branch.clone())
                        * s.clone(),
                ));
            }

            // RLP constraints:
            let s_bytes0_prev = meta.query_advice(s_main.bytes[0], Rotation::prev());
            let short_remainder = s_rlp1_prev.clone() - c192.clone() - s_rlp2_prev.clone()
                + c128.clone()
                - one.clone();
            let long_remainder = s_rlp2_prev - s_bytes0_prev + c128.clone() - one.clone();
            let long_value_len = s_rlp2_cur.clone() - c128.clone() + one.clone() + one.clone();

            let short_short_check = short_remainder.clone() - one.clone();
            let long_long_check = long_remainder - long_value_len.clone();
            let short_long_check = short_remainder - long_value_len.clone();
            /*
            Note: long short is not possible because the key has at most 32 bytes and
            short value means only 1 byte which (together with RLP meta
            bytes) cannot go over 55 bytes.
            */

            let long_value_check = s_rlp1_cur - s_rlp2_cur + one.clone();

            /*
            When the leaf is short (first key byte in `s_main.bytes[0]` in the leaf key row) and the value
            is short (first value byte in `s_main.rlp1` in the leaf value row), we need to check that:
            `s_rlp1_prev - 192 - s_rlp2_prev + 128 - 1 - 1 = 0`.

            The first `-1` presents the byte occupied by `s_rlp2_prev`.
            The second `-1` presents the length of the value which is 1 because the value is short in this case.

            Example:
            `[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]`

            In the example: `34 = 226 - 192` gives the length of the RLP stream. `32 = 160 - 128` gives the length
            of the key. That means there are 34 bytes after the first byte, 32 of these are occupied by the key,
            1 is occupied by `s_rlp2_prev`, and 1 is occupied by the value.
            */
            constraints.push((
                "RLP leaf short value short",
                q_enable.clone() * short_short_check * is_leaf_short.clone() * is_short.clone(),
            ));

            /*
            When the leaf is long (first key byte in `s_main.bytes[1]` in the leaf key row) and the value
            is long (first value byte in `s_main.bytes[0]` in the leaf value row), we need to check that:
            `s_rlp2_prev - s_bytes0_prev + 128 - 1 - (s_rlp2_cur - 128 + 1 + 1) = 0`.

            The expression `s_rlp2_prev - s_bytes0_prev + 128 - 1` gives us the number of bytes that are to be left
            in the value. The expression `s_rlp2_cur - 128 + 1 + 1` gives us the number of bytes in the leaf.

            Note that there is an additional constraint to ensure `s_main.rlp1 = s_main.rlp2 + 1`.

            Example:
            `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
            `[161 160 187 239 170 18 88 1 56 188 38 60 149 117 120 38 223 78 36 235 129 201 170 170 170 170 170 170 170 170 170 170 170 170 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]`

            67 is the number of bytes after `s_main.rlp2`. `160 - 128 + 1` is the number of bytes that are occupied
            by the key and the byte that stores key length.
            In the next row, we have `32 = 160 - 128` bytes after `s_main.rlp2`, but we need to take into
            account also the two bytes `s_main.rlp1` and `s_main.rlp2`.
            */
            constraints.push((
                "RLP leaf long value long",
                q_enable.clone() * long_long_check * is_leaf_long.clone() * is_long.clone(),
            ));

            /*
            When the leaf is short (first key byte in `s_main.bytes[0]` in the leaf key row) and the value
            is long (first value byte in `s_main.bytes[0]` in the leaf value row), we need to check that:
            `s_rlp1_prev - 192 - s_rlp2_prev + 128 - 1 - (s_rlp2_cur - 128 + 1 + 1) = 0`.

            The expression `s_rlp1_prev - 192 - s_rlp2_prev + 128 - 1` gives us the number of bytes that are to be left
            in the value. The expression `s_rlp2_cur - 128 + 1 + 1` gives us the number of bytes in the leaf.
            */
            constraints.push((
                "RLP leaf short value long",
                q_enable.clone() * short_long_check * is_leaf_short.clone() * is_long.clone(),
            ));

            /*
            When the leaf is long (first key byte in `s_main.bytes[1]` in the leaf key row)
            we need to ensure that `s_main.rlp1 = s_main.rlp2 + 1`.
            */
            constraints.push((
                "RLP long value check",
                q_enable.clone() * long_value_check * is_long.clone(),
            ));

            /*
            When the leaf is in the last level of the trie and the value is short, 
            we need to ensure that `s_main.rlp2 = 32`.

            Note that in this case we do not have the length of the key stored in `s_main.rlp2` or `s_main.bytes[0]`.
            
            Example: `[194,32,1]`
            */
            constraints.push((
                "RLP check last level or one nibble & short value",
                q_enable.clone()
                    * (s_rlp1_prev.clone() - Expression::Constant(F::from(194)))
                    * (last_level.clone() + one_nibble.clone())
                    * is_short.clone(),
            ));

            let last_level_or_one_nibblelong_check = s_rlp1_prev.clone() - c192.clone()
                - one.clone() - long_value_len;

            /*
            When the leaf is in the last level of the trie and the value is long or there is one nibble in the key,
            we need to check:
            `s_rlp1_prev - 192 - 1  - (s_rlp2_cur - 128 + 1 + 1) = 0`.

            `s_rlp1_prev - 192 - 1` gives us the number of bytes that are to be in the leaf value row, while
            s_rlp2_cur - 128 + 1 + 1 gives us the number of bytes in the leaf value row.

            Note that in this case we do not have the length of the key stored in `s_main.rlp2` or `s_main.bytes[0]`.

            Example:
            `[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]`
            */
            constraints.push((
                "RLP check last level or one nibble & long value",
                q_enable.clone()
                    * last_level_or_one_nibblelong_check
                    * (last_level.clone() + one_nibble)
                    * is_long.clone(),
            ));
 
            let empty_trie_hash: Vec<u8> = vec![
                86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72,
                224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
            ];
            let mut sel = meta.query_advice(denoter.sel1, Rotation::cur());

            let mut rot_into_storage_root = -4;
            if !is_s {
                sel = meta.query_advice(denoter.sel2, Rotation::cur());
                rot_into_storage_root = -5;
            }

            /*
            `sel = 1` in the leaf value row when the leaf is only a placeholder (it is added or deleted and
            thus there is no leaf in either `S` or `C` proof).
            This selector is used to trigger off the constraint for the leaf hash being the same as
            the storage trie root (because leaf in this case is just a placeholder) in
            `storage_root_in_account_leaf.rs`.
            These constraints prevent setting `sel = 1` (and thus triggering off the constraint for the leaf hash
            to be the storage trie) in cases when the storage trie is not empty.
            */
            for (ind, col) in s_main.bytes.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation(rot_into_storage_root));
                constraints.push((
                    "If placeholder leaf without branch (sel = 1), then storage trie is empty",
                    q_enable.clone()
                        * sel.clone()
                        * is_leaf_without_branch.clone()
                        * (s.clone() - Expression::Constant(F::from(empty_trie_hash[ind] as u64))),
                ));
            }

            constraints
        });

        /*
        It needs to be checked that the hash of a leaf is in the parent node. We do this by a lookup
        into keccak table: `lookup(leaf_hash_rlc, parent_node_mod_child_rlc)`. 
        */
        meta.lookup_any("Leaf hash in parent", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * not_first_level * is_leaf;

            let not_hashed = meta.query_advice(accs.acc_c.rlc, Rotation::prev());

            let rlc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            let mut placeholder_leaf = meta.query_advice(denoter.sel1, Rotation(rot));
            if !is_s {
                placeholder_leaf = meta.query_advice(denoter.sel2, Rotation(rot));
            }

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in `storage_root_in_account_leaf.rs`.
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            /*
            If `sel = 1`, the leaf is only a placeholder (the leaf is being added or deleted)
            and we do not check the hash of it.
            */
            let mut constraints = vec![];
            constraints.push((
                q_enable.clone()
                    * rlc
                    * (one.clone() - placeholder_leaf.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * (one.clone() - not_hashed.clone())
                    * (one.clone() - is_branch_placeholder.clone()),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            let mut mod_node_hash_rlc_cur = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
            }
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * mod_node_hash_rlc_cur
                    * (one.clone() - placeholder_leaf.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * (one.clone() - not_hashed.clone())
                    * (one.clone() - is_branch_placeholder.clone()),
                keccak_table_i,
            ));

            constraints
        });

        /*
        When the leaf is not hashed (shorter than 32 bytes), it needs to be checked that its RLC
        is the same as the RLC of the modified node in the parent branch.

        When leaf is not hashed, the `mod_node_hash_rlc` stores the RLC of the leaf bytes
        (instead of the RLC of leaf hash). So we take the leaf RLC and compare it to the value
        stored in `mod_node_hash_rlc` in the parent branch.

        Note: `branch_parallel.rs` checks that there are 0s in `*_bytes` after the last
        byte of the non-hashed branch child (otherwise some corrupted RLC could be provided).
        */
        meta.create_gate("Non-hashed leaf in parent", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * not_first_level * is_leaf;

            let not_hashed = meta.query_advice(accs.acc_c.rlc, Rotation::prev());

            let rlc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            let mut placeholder_leaf = meta.query_advice(denoter.sel1, Rotation(rot));
            if !is_s {
                placeholder_leaf = meta.query_advice(denoter.sel2, Rotation(rot));
            }

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in storage_root_in_account_leaf.
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            let mut mod_node_hash_rlc_cur = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
            }

            let mut constraints = vec![];
            constraints.push((
                "non-hashed",
                q_enable.clone()
                    * (rlc - mod_node_hash_rlc_cur)
                    * (one.clone() - placeholder_leaf.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * not_hashed.clone()
                    * (one.clone() - is_branch_placeholder.clone()),
            ));

            constraints
        });

        /*
        Lookup for case when there is a placeholder branch - in this case we need to
        check the hash to correspond to the modified node of the branch above the placeholder branch.
        */
        meta.lookup_any("Leaf hash in parent (branch placeholder)", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * not_first_level * is_leaf;

            let mut rlc = meta.query_advice(accs.acc_s.rlc, Rotation::prev());
            let mut mult = meta.query_advice(accs.acc_s.mult, Rotation::prev());

            let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());
            rlc = rlc + s_rlp1 * mult.clone();
            mult = mult * acc_r;

            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * mult.clone();
            mult = mult * acc_r;

            for col in s_main.bytes.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                rlc = rlc + s * mult.clone();
                mult = mult * acc_r;
            }

            let mut sel = meta.query_advice(denoter.sel1, Rotation(rot));
            if !is_s {
                sel = meta.query_advice(denoter.sel2, Rotation(rot));
            }

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in storage_root_in_account_leaf.
            let is_leaf_without_branch_after_placeholder = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_account - BRANCH_ROWS_NUM),
            );
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            /*
            Note: `sel1` and `sel2` in branch children: denote whether there is no leaf at
            `is_modified` (when value is added or deleted from trie).
            */

            /*
            If `sel = 1`, there is no leaf at this position (value is being added or
            deleted) and we do not check the hash of it.
            */
            let mut constraints = vec![];
            constraints.push((
                q_enable.clone()
                    * rlc
                    * (one.clone() - sel.clone())
                    * (one.clone() - is_leaf_without_branch_after_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_branch_placeholder.clone(),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            let mut mod_node_hash_rlc = meta.query_advice(
                accs.s_mod_node_rlc,
                Rotation(rot_into_init - 3), /* -3 to get from init branch into the previous
                                              * branch (last row), note that -2 is needed
                                              * because of extension nodes */
            );
            if !is_s {
                mod_node_hash_rlc =
                    meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_init - 3));
            }

            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * mod_node_hash_rlc
                    * (one.clone() - sel.clone())
                    * (one.clone() - is_leaf_without_branch_after_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_branch_placeholder.clone(),
                keccak_table_i,
            ));

            constraints
        });

        /*
        Note: For cases when storage leaf is in the first storage level, the
        constraints are in `storage_root_in_account_leaf.rs`.
        */

        let sel = |meta: &mut VirtualCells<F>| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            not_first_level * is_leaf
        };

        /*
        Range lookups ensure that `s_main`, `s_main.rlp1`, `s_main.rlp2` columns are all bytes (between 0 - 255).
        */
        range_lookups(
            meta,
            sel,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel,
            [s_main.rlp1, s_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        /*
        /*
        There are 0s in `s_main.bytes` after the last value byte.
        */
        for ind in 0..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel,
                ind + 1,
                s_main.rlp2,
                s_main.bytes[ind],
                128,
                fixed_table,
            )
        }
        */

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        pv: &mut ProofVariables<F>,
        offset: usize,
        is_s: bool,
    ) {
        let row_prev = &witness[offset - 1];
        let row = &witness[offset];

        // Info whether leaf value is 1 byte or more:
        let mut is_long = false;
        if row_prev.get_byte(0) == 248 {
            // whole leaf is in long format (3 RLP meta bytes)
            let key_len = row_prev.get_byte(2) - 128;
            if row_prev.get_byte(1) - key_len - 1 > 1 {
                is_long = true;
            }
        } else if row_prev.get_byte(1) < 128 {
            // last_level or one_nibble
            let leaf_len = row_prev.get_byte(0) - 192;
            if leaf_len - 1 > 1 {
                is_long = true;
            }
        } else {
            let leaf_len = row_prev.get_byte(0) - 192;
            let key_len = row_prev.get_byte(1) - 128;
            if leaf_len - key_len - 1 > 1 {
                is_long = true;
            }
        }
        // Short means there is only one byte for value (no RLP specific bytes).
        // Long means there is more than one byte for value which brings two
        // RLP specific bytes, like: 161 160 ... for 32-long value.
        let mut typ = "short";
        if is_long {
            typ = "long";
        } 
        mpt_config.assign_long_short(region, typ, offset).ok();

        // Leaf RLC
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut pv.acc_s,
            &mut pv.acc_mult_s,
            0,
            HASH_WIDTH + 2,
        );

        pv.acc_c = F::zero();
        pv.acc_mult_c = F::one();
        // Leaf value RLC
        let mut start = 0;
        if is_long {
            start = 2;
        }
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut pv.acc_c,
            &mut pv.acc_mult_c,
            start,
            HASH_WIDTH + 2,
        );

        let empty_trie_hash: Vec<u8> = vec![
            86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192,
            248, 110, 91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181,
            227, 99, 180, 33,
        ];
        if is_s {
            // Store leaf value RLC into rlc1 to be later set in leaf value C row (to enable lookups):
            pv.rlc1 = pv.acc_c;

            /*
            account leaf storage codehash S <- rotate here
            account leaf storage codehash C
            account leaf in added branch
            leaf key S
            leaf value S <- we are here
            leaf key C
            leaf value C
            */
            let row_prev = &witness[offset - 4];
            if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                && row_prev.s_hash_bytes() == empty_trie_hash
            {
                // Leaf is without branch and it is just a placeholder.
                region.assign_advice(
                    || "assign sel1".to_string(),
                    mpt_config.denoter.sel1,
                    offset,
                    || Ok(F::one()),
                ).ok();
            }
        } else {
            region.assign_advice(
                || "assign key_rlc into key_rlc_mult".to_string(),
                mpt_config.accumulators.key.mult,
                offset,
                || Ok(pv.rlc2),
            ).ok();
            region.assign_advice(
                || "assign leaf value S into mult_diff".to_string(),
                mpt_config.accumulators.mult_diff,
                offset,
                || Ok(pv.rlc1),
            ).ok();

            /*
            account leaf storage codehash S
            account leaf storage codehash C <- rotate here
            account leaf in added branch
            leaf key S
            leaf value S
            leaf key C
            leaf value C <- we are here
            */
            let row_prev = &witness[offset - 5];
            if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
                && row_prev.s_hash_bytes() == empty_trie_hash
            {
                // Leaf is without branch and it is just a placeholder.
                region.assign_advice(
                    || "assign sel2".to_string(),
                    mpt_config.denoter.sel2,
                    offset,
                    || Ok(F::one()),
                ).ok();
            }
        }

        mpt_config.assign_acc(
            region,
            pv.acc_s, // leaf RLC
            pv.acc_mult_s,
            pv.acc_c, // leaf value RLC
            F::zero(),
            offset,
        ).ok();
    }
}