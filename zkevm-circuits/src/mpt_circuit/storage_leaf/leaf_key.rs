use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols},
    mpt_circuit::helpers::{compute_rlc, get_bool_constraint, mult_diff_lookup, range_lookups},
    mpt_circuit::param::{
        BRANCH_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
        IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, NIBBLES_COUNTER_POS,
        POWER_OF_RANDOMNESS_LEN, RLP_NUM, S_START,
    },
    mpt_circuit::witness_row::{MptWitnessRow, MptWitnessRowType},
    mpt_circuit::{
        columns::DenoteCols, helpers::{key_len_lookup, get_is_inserted_extension_node}, FixedTableTag, MPTConfig, ProofValues,
    },
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
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

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
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

`last_level`
[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

`one_nibble`:
[194 48 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[194 48 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

`s_mod_node_rlc` (`flag1`) and `c_mod_node_rlc` (`flag2`) columns store the information of what
kind of case we have:
 `flag1: 1, flag2: 0`: `is_long`
 `flag1: 0, flag2: 1`: `is_short`
 `flag1: 1, flag2: 1`: `last_level`
 `flag1: 0, flag0: 1`: `one_nibble`

The constraints in `leaf_key.rs` apply to `LEAF_KEY_S` and `LEAF_KEY_C` rows.
*/

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        denoter: DenoteCols<F>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        is_s: bool,
        check_zeros: bool,
    ) -> Self {
        let config = LeafKeyConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());
        let c32 = Expression::Constant(F::from(32));
        let c48 = Expression::Constant(F::from(48));
        let c64 = Expression::Constant(F::from(64));
        let c128 = Expression::Constant(F::from(128));

        let mut rot_into_init = -19;
        let mut rot_into_account = -1;
        if !is_s {
            rot_into_init = -21;
            rot_into_account = -3;
        }

        /*
        Checking the leaf RLC is ok - this value is then taken in the next row, where
        leaf value is added to the RLC. Finally, the lookup is used to check the hash that
        corresponds to the RLC is in the parent branch.
        */
        meta.create_gate("Storage leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());

            let last_level = flag1.clone() * flag2.clone();
            let is_long = flag1.clone() * (one.clone() - flag2.clone());
            let is_short = (one.clone() - flag1.clone()) * flag2.clone();
            let one_nibble = (one.clone() - flag1.clone()) * (one.clone() - flag2.clone());

            let is_leaf_in_first_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));
            let mut sel = meta.query_advice(denoter.sel1, Rotation(rot_into_init + 1));
            if !is_s {
                sel = meta.query_advice(denoter.sel2, Rotation(rot_into_init + 1));
            }
            let mut leaf_without_branch_and_is_placeholder =
                meta.query_advice(denoter.sel1, Rotation(1));
            if !is_s {
                leaf_without_branch_and_is_placeholder =
                    meta.query_advice(denoter.sel2, Rotation(1));
            }

            let is_leaf_placeholder = (one.clone() - is_leaf_in_first_level) * sel
                + leaf_without_branch_and_is_placeholder;

            /*
            When `is_long` (the leaf value is longer than 1 byte), `s_main.rlp1` needs to be 248.

            Example:
            `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
            */
            constraints.push((
                "is_long: s_rlp1 = 248",
                q_enable.clone()
                    * (one.clone() - is_leaf_placeholder.clone())
                    * is_long.clone()
                    * (s_rlp1.clone() - c248),
            ));

            /*
            When `last_level`, there is no nibble stored in the leaf key, it is just the value
            `32` in `s_main.rlp2`. In the `getProof` output, there is then the value stored immediately
            after `32`. However, in the MPT witness, we have value in the next row, so there are 0s
            in `s_main.bytes` (we do not need to check `s_main.bytes[i]` to be 0 due to how the RLC
            constraints are written).

            Example:
            `[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
            */
            constraints.push((
                "last_level: s_rlp2 = 32",
                q_enable.clone()
                    * last_level.clone()
                    * (one.clone() - is_leaf_placeholder.clone())
                    * (s_rlp2.clone() - c32.clone()),
            ));

            /*
            The two values that store the information about what kind of case we have need to be
            boolean.
            */
            constraints.push((
                "flag1 is boolean",
                get_bool_constraint(q_enable.clone(), flag1),
            ));

            constraints.push((
                "flag2 is boolean",
                get_bool_constraint(q_enable.clone(), flag2),
            ));

            // If leaf in last level, it contains only s_rlp1 and s_rlp2, while s_main.bytes
            // are 0.
            let rlc_last_level_or_one_nibble = s_rlp1 + s_rlp2 * power_of_randomness[0].clone();

            let mut rlc = rlc_last_level_or_one_nibble.clone()
                + compute_rlc(
                    meta,
                    s_main.bytes.to_vec(),
                    1,
                    one.clone(),
                    0,
                    power_of_randomness.clone(),
                );

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            // c_rlp2 can appear if long and if no branch above leaf
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            rlc = rlc
                + c_rlp1
                    * power_of_randomness[POWER_OF_RANDOMNESS_LEN - 1].clone()
                    * power_of_randomness[1].clone();
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
                "Leaf key RLC (short or long)",
                q_enable.clone()
                    * (is_short + is_long)
                    * (one.clone() - is_leaf_placeholder.clone())
                    * (rlc - acc.clone()),
            ));

            /*
            We need to ensure that the RLC of the row is computed properly for `last_level` and
            `one_nibble`. We compare the computed value with the value stored in `accumulators.acc_s.rlc`.

            `last_level` and `one_nibble` cases have one RLP byte (`s_rlp1`) and one byte (`s_rlp2`)
            where it is 32 (for `last_level`) or `48 + last_nibble` (for `one_nibble`).
            */
            constraints.push((
                "Leaf key RLC (last level or one nibble)",
                q_enable
                    * (last_level + one_nibble)
                    * (one.clone() - is_leaf_placeholder)
                    * (rlc_last_level_or_one_nibble - acc),
            ));

            constraints
        });

        let sel_short = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let is_short = (one.clone() - flag1) * flag2;

            q_enable * is_short
        };
        let sel_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let is_long = flag1 * (one.clone() - flag2);

            q_enable * is_long
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
            key_len_lookup(
                meta,
                sel_short,
                32,
                s_main.rlp2,
                c_main.rlp1,
                128,
                fixed_table,
            );

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
            key_len_lookup(
                meta,
                sel_long,
                33,
                s_main.bytes[0],
                c_main.rlp2,
                128,
                fixed_table,
            );
        }

        /*
        The intermediate RLC value of this row is stored in `accumulators.acc_s.rlc`.
        To compute the final leaf RLC in `LEAF_VALUE` row, we need to know the multiplier to be used
        for the first byte in `LEAF_VALUE` row too. The multiplier is stored in `accumulators.acc_s.mult`.
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
        We need to ensure that the storage leaf is at the key specified in `key_rlc` column (used
        by MPT lookup). To do this we take the key RLC computed in the branches above the leaf
        and add the remaining bytes (nibbles) stored in the leaf.

        We also ensure that the number of all nibbles (in branches / extension nodes above
        the leaf and in the leaf) is 64.
        */
        meta.create_gate(
            "Storage leaf key RLC & nibbles count (branch not placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
                let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());

                let last_level = flag1.clone() * flag2.clone();
                let is_long = flag1.clone() * (one.clone() - flag2.clone());
                let is_short = (one.clone() - flag1.clone()) * flag2.clone();
                let one_nibble = (one.clone() - flag1) * (one.clone() - flag2);

                let is_leaf_in_first_storage_level =
                    meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));
                let mut sel = meta.query_advice(denoter.sel1, Rotation(rot_into_init + 1));
                if !is_s {
                    sel = meta.query_advice(denoter.sel2, Rotation(rot_into_init + 1));
                }
                let mut leaf_without_branch_and_is_placeholder = meta.query_advice(denoter.sel1, Rotation(1));
                if !is_s {
                    leaf_without_branch_and_is_placeholder = meta.query_advice(denoter.sel2, Rotation(1));
                }

                let is_leaf_placeholder = (one.clone() - is_leaf_in_first_storage_level.clone()) * sel
                    + leaf_without_branch_and_is_placeholder;

                // key rlc is in the first branch node (not branch init)
                let mut rot = -18;
                if !is_s {
                    rot = -20;
                }

                let mut key_rlc_acc_start = meta.query_advice(accs.key.rlc, Rotation(rot));
                let mut key_mult_start = meta.query_advice(accs.key.mult, Rotation(rot));

                /*
                `key_rlc_acc_start = 0` if leaf in first storage level
                `key_mult_start = 1` if leaf in first storage level
                */
                key_rlc_acc_start = key_rlc_acc_start.clone() * (one.clone() - is_leaf_in_first_storage_level.clone());
                key_mult_start = key_mult_start.clone() * (one.clone() - is_leaf_in_first_storage_level.clone()) + is_leaf_in_first_storage_level.clone();

                /*
                `c16` and `c1` specify whether in the branch above the leaf the `modified_nibble`
                had to be multiplied by 16 or by 1 for the computation the key RLC.
                */
                let mut is_c16 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let mut is_c1 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                /*
                `c16 = 0, c1 = 1` if leaf in first storage level, because we do not have the branch above
                and we need to multiply the first nibble by 16 (as it would be `c1` in the branch above)
                */
                is_c16 = is_c16.clone() * (one.clone() - is_leaf_in_first_storage_level.clone());
                is_c1 = is_c1.clone() * (one.clone() - is_leaf_in_first_storage_level.clone()) + is_leaf_in_first_storage_level.clone();

                let mut is_branch_placeholder =
                    meta.query_advice(s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM], Rotation(rot_into_init));
                if !is_s {
                    is_branch_placeholder =
                        meta.query_advice(s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], Rotation(rot_into_init));
                }

                // `is_branch_placeholder = 0` when in first level
                is_branch_placeholder = is_branch_placeholder.clone() * (one.clone() - is_leaf_in_first_storage_level.clone());

                /*
                If the last branch is placeholder (the placeholder branch is the same as its
                parallel counterpart), there is a branch `modified_node` nibble already
                incorporated in `key_rlc`. That means we need to ignore the first nibble here
                (in leaf key).
                */

                // For short RLP (the key starts at `s_main.bytes[0]`):

                // If `c16`, we have one nibble+48 in `s_main.bytes[0]`.
                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                let mut key_rlc_acc_short = key_rlc_acc_start.clone()
                    + (s_bytes0.clone() - c48.clone()) * key_mult_start.clone() * is_c16.clone();
                let mut key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16.clone();
                key_mult = key_mult + key_mult_start.clone() * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[0]`.
                This is because `is_c1` in the branch above means there is an even number of nibbles left
                and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                specifying the length) of the key is 32.
                */
                constraints.push((
                    "Leaf key RLC s_bytes0 = 32 (short)",
                    q_enable.clone()
                        * (s_bytes0.clone() - c32.clone())
                        * (one.clone() - is_leaf_placeholder.clone())
                        * is_c1.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * is_short.clone(),
                ));

                let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                key_rlc_acc_short = key_rlc_acc_short + s_bytes1 * key_mult.clone();

                for ind in 2..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc_short =
                        key_rlc_acc_short + s * key_mult.clone() * power_of_randomness[ind - 2].clone();
                }

                // c_rlp1 can appear if no branch above the leaf
                let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
                key_rlc_acc_short =
                    key_rlc_acc_short + c_rlp1.clone() * key_mult * power_of_randomness[30].clone();

                let key_rlc = meta.query_advice(accs.key.rlc, Rotation::cur());

                /*
                We need to ensure the leaf key RLC is computed properly. We take the key RLC value
                from the last branch and add the bytes from position
                `s_main.bytes[0]` up at most to `c_main.rlp1`. We need to ensure that there are 0s
                after the last key byte, this is done by `key_len_lookup`.

                The computed value needs to be the same as the value stored `key_rlc` column.

                `is_short` example:
                [226,160,59,138,106,70,105,186,37,13,38[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]

                Note: No need to distinguish between `c16` and `c1` here as it was already
                when computing `key_rlc_acc_short`.
                */
                constraints.push((
                    "Key RLC (short)",
                    q_enable.clone()
                        * (key_rlc_acc_short - key_rlc.clone())
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * is_short.clone(),
                ));

                // For long RLP (key starts at `s_main.bytes[1]`):

                // If `is_c16`, we have nibble+48 in `s_main.bytes[1]`.
                let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                let mut key_rlc_acc_long = key_rlc_acc_start.clone()
                    + (s_bytes1.clone() - c48.clone()) * key_mult_start.clone() * is_c16.clone();
                let mut key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16.clone();
                key_mult = key_mult + key_mult_start.clone() * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[1]`.
                This is because `is_c1` in the branch above means there is an even number of nibbles left
                and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                specifying the length) of the key is 32.
                */
                constraints.push((
                    "Leaf key acc s_bytes1 = 32 (long)",
                    q_enable.clone()
                        * (s_bytes1 - c32.clone())
                        * is_c1.clone()
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * is_long.clone(),
                ));

                let s_bytes2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
                key_rlc_acc_long = key_rlc_acc_long + s_bytes2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc_long =
                        key_rlc_acc_long + s * key_mult.clone() * power_of_randomness[ind - 3].clone();
                }

                key_rlc_acc_long =
                    key_rlc_acc_long + c_rlp1 * key_mult.clone() * power_of_randomness[29].clone();
                // c_rlp2 can appear if no branch above the leaf
                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                key_rlc_acc_long =
                    key_rlc_acc_long + c_rlp2 * key_mult * power_of_randomness[30].clone();

                /*
                We need to ensure the leaf key RLC is computed properly. We take the key RLC value
                from the last branch and add the bytes from position
                `s_main.bytes[1]` up at most to `c_main.rlp2`. We need to ensure that there are 0s
                after the last key byte, this is done by `key_len_lookup`.

                The computed value needs to be the same as the value stored `key_rlc` column.

                `is_long` example:
                `[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...`

                Note: No need to distinguish between `c16` and `c1` here as it was already
                when computing `key_rlc_acc_long`.
                */
                constraints.push((
                    "Key RLC (long)",
                    q_enable.clone()
                        * (key_rlc_acc_long - key_rlc.clone())
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * is_long.clone(),
                ));

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());

                /*
                When the leaf is in the last level there are no nibbles stored in the key and
                `s_main.rlp2 = 32`.
                */
                constraints.push((
                    "Leaf key acc s_rlp2 = 32 (last level)",
                    q_enable.clone()
                        * (s_rlp2 - c32.clone())
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * last_level.clone(),
                ));

                /*
                We need to ensure the leaf key RLC is computed properly.
                When the leaf is in the last level we simply take the key RLC value
                from the last branch and this is the final key RLC value as there is no
                nibble in the leaf.

                The computed value needs to be the same as the value stored `key_rlc` column.

                Last level example:
		        `[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]`
                */
                constraints.push((
                    "Key RLC (last level)",
                    q_enable.clone()
                        * (key_rlc_acc_start.clone() - key_rlc.clone()) // key_rlc has already been computed
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * last_level.clone(),
                ));

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
                let key_rlc_one_nibble = key_rlc_acc_start
                    + (s_rlp2 - c48.clone()) * key_mult_start;

                /*
                We need to ensure the leaf key RLC is computed properly.
                When there is only one nibble in the leaf, we take the key RLC value
                from the last branch and add the last remaining nibble stored in `s_main.rlp2`.

                The computed value needs to be the same as the value stored `key_rlc` column.

                One nibble example short value:
                `[194,48,1]`

                One nibble example long value:
                `[227,48,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]`
                */
                constraints.push((
                    "Key RLC (one nibble)",
                    q_enable.clone()
                        * (key_rlc_one_nibble - key_rlc)
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * one_nibble.clone(),
                ));

                // Nibbles count:
                let mut nibbles_count = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                // nibbles_count = 0 if in first storage level
                nibbles_count = nibbles_count.clone() * (one.clone() - is_leaf_in_first_storage_level);

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
                let leaf_nibbles_long = ((s_bytes0.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone())) * is_c1.clone() +
                    ((s_bytes0 - c128.clone()) * (one.clone() + one.clone()) - one.clone()) * is_c16.clone();
                let leaf_nibbles_short = ((s_rlp2.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone())) * is_c1 +
                    ((s_rlp2 - c128.clone()) * (one.clone() + one.clone()) - one.clone()) * is_c16;
                let leaf_nibbles_last_level = Expression::Constant(F::zero());
                let leaf_nibbles_one_nibble = one.clone();

                let leaf_nibbles = leaf_nibbles_long * is_long + leaf_nibbles_short * is_short
                    + leaf_nibbles_last_level * last_level + leaf_nibbles_one_nibble * one_nibble;

                /* 
                Checking the total number of nibbles is to prevent having short addresses
                which could lead to a root node which would be shorter than 32 bytes and thus not hashed. That
                means the trie could be manipulated to reach a desired root.
                */
                constraints.push((
                    "Total number of storage address nibbles is 64 (not first level, not branch placeholder)",
                    q_enable
                        * (one.clone() - is_leaf_placeholder)
                        * (one.clone() - is_branch_placeholder)
                        // Note: we need to check the number of nibbles being 64 for non_existing_account_proof too
                        // (even if the address being checked here might be the address of the wrong leaf)
                        * (nibbles_count + leaf_nibbles - c64.clone()),
                ));

                constraints
            },
        );

        /*
        For leaf under the placeholder branch we would not need to check the key RLC -
        this leaf is something we did not ask for, it is just a leaf that happened to be
        at the place where adding a new leaf causes adding a new branch.
        For example, when adding a leaf `L` causes that a leaf `L1`
        (this will be the leaf under the branch placeholder)
        is replaced by a branch, we get a placeholder branch at `S` side
        and leaf `L1` under it. However, the key RLC needs to be compared for leaf `L`,
        because this is where the modification takes place.
        In delete, the situation is turned around.

        However, we also check that the key RLC for `L1` is computed properly because
        we need `L1` key RLC for the constraints for checking that leaf `L1` is the same
        as the drifted leaf in the branch parallel. This can be checked by
        comparing the key RLC of the leaf before being replaced by branch and the key RLC
        of this same leaf after it drifted into a branch.
        Constraints for this are in `leaf_key_in_added_branch.rs`.

        Note that the hash of a leaf `L1` needs to be checked to be in the branch
        above the placeholder branch - this is checked in `leaf_value.rs`.
        */
        meta.create_gate("Storage leaf key RLC (after placeholder)", |meta| {
            /*
            Note: `last_level` cannot occur in a leaf after placeholder branch, because being
            after placeholder branch means this leaf drifted down into a new branch (in a parallel
            proof) and thus cannot be in the last level.
            */

            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());
            let is_long = flag1.clone() * (one.clone() - flag2.clone());
            let is_short = (one.clone() - flag1.clone()) * flag2.clone();
            let one_nibble = (one.clone() - flag1) * (one.clone() - flag2);

            // Note: key RLC is in the first branch node (not branch init).
            let rot_level_above = rot_into_init + 1 - BRANCH_ROWS_NUM;

            let is_first_storage_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_init - 1));

            let is_leaf_in_first_level =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_into_init),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
            }

            /*
            Retrieve the key RLC and multiplier from above the placeholder branch.
            */
            let key_rlc_acc_start = meta.query_advice(accs.key.rlc, Rotation(rot_level_above))
                * (one.clone() - is_first_storage_level.clone());
            let key_mult_start = meta.query_advice(accs.key.mult, Rotation(rot_level_above))
                * (one.clone() - is_first_storage_level.clone())
                + is_first_storage_level.clone();

            /*
            Note that when `is_first_storage_level`, it is always `is_c1 = 1` because
            there are all 32 bytes in a key.
            */
            let is_c16 = (one.clone() - is_first_storage_level.clone())
                * meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_level_above - 1),
                );
            let is_c1 = (one.clone() - is_first_storage_level.clone())
                * meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_level_above - 1),
                )
                + is_first_storage_level.clone();

            // When short RLP, key starts at `s_main.bytes[0]`:

            // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[0]`.
            let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
            let mut key_rlc_acc_short = key_rlc_acc_start.clone()
                + (s_bytes0.clone() - c48.clone()) * key_mult_start.clone() * is_c16.clone();
            let key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16.clone()
                + key_mult_start.clone() * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            /*
            When extension node is inserted, the leaf is only a placeholder (as well as branch) -
            we need to compare the hash of the extension node in the inserted extension node row
            to the hash in the branch above the placeholder branch
            (see `extension_node_inserted.rs`).
            */
            let is_inserted_ext_node = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_into_init, is_s);

            /*
            If `is_c1 = 1` which means there is an even number of nibbles stored in a leaf,
            we have 32 in `s_main.bytes[0]`.
            */
            constraints.push((
                "Leaf key acc s_bytes0 (short)",
                q_enable.clone()
                    * (s_bytes0.clone() - c32.clone())
                    * is_c1.clone()
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (one.clone() - is_inserted_ext_node.clone())
                    * is_short.clone(),
            ));

            let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
            key_rlc_acc_short = key_rlc_acc_short + s_bytes1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_acc_short =
                    key_rlc_acc_short + s * key_mult.clone() * power_of_randomness[ind - 2].clone();
            }

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            key_rlc_acc_short = key_rlc_acc_short
                + c_rlp1.clone() * key_mult.clone() * power_of_randomness[30].clone();

            let key_rlc = meta.query_advice(accs.key.rlc, Rotation::cur());

            /*
            When `is_short` the first key byte is at `s_main.bytes[0]`. We retrieve the key RLC from the
            branch above the branch placeholder and add the nibbles stored in a leaf.
            The computed key RLC needs to be the same as the value stored at `accumulators.key.rlc`.

            `is_short`:
            `[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]`

            `is_long`:
            `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`

            Note: No need to distinguish between `is_c16` and `is_c1` here as it was already
            when computing `key_rlc_acc_short`.
            */
            constraints.push((
                "Key RLC (short)",
                q_enable.clone()
                    * (key_rlc_acc_short - key_rlc.clone())
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (one.clone() - is_inserted_ext_node.clone())
                    * is_short.clone(),
            ));

            // When long RLP: key starts at `s_main.bytes[1]`:

            // If `is_c16 = 1`, we have nibble+48 in `s_main.bytes[1]`.
            let mut key_rlc_acc_long = key_rlc_acc_start
                + (s_bytes1.clone() - c48.clone()) * key_mult_start * is_c16.clone();

            /*
            If `is_c1 = 1` which means there is an even number of nibbles stored in a leaf,
            we have 32 in `s_main.bytes[1]`.
            */
            constraints.push((
                "Leaf key acc s_bytes1 (long)",
                q_enable.clone()
                    * (s_bytes1 - c32.clone())
                    * is_c1.clone()
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (one.clone() - is_inserted_ext_node.clone())
                    * is_long.clone(),
            ));

            let s_bytes2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + s_bytes2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_acc_long =
                    key_rlc_acc_long + s * key_mult.clone() * power_of_randomness[ind - 3].clone();
            }

            key_rlc_acc_long =
                key_rlc_acc_long + c_rlp1 * key_mult.clone() * power_of_randomness[29].clone();

            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            key_rlc_acc_long =
                key_rlc_acc_long + c_rlp2 * key_mult * power_of_randomness[30].clone();

            /*
            When `is_long` the first key byte is at `s_main.bytes[1]`. We retrieve the key RLC from the
            branch above the branch placeholder and add the nibbles stored in a leaf.
            The computed key RLC needs to be the same as the value stored at `accumulators.key.rlc`.

            `is_short`:
            `[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]`

            `is_long`:
            `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`

            No need to distinguish between `is_c16` and `is_c1` here as it was already
            when computing `key_rlc_acc_long`.
            */
            constraints.push((
                "Key RLC (long)",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc)
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone())
                    * (one.clone() - is_inserted_ext_node.clone())
                    * is_long.clone(),
            ));

            /*
            Note: When the leaf is after the placeholder branch, it cannot be in the last level
            otherwise it would not be possible to add a branch placeholder.
            */

            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
            let leaf_nibbles_long = ((s_bytes0.clone() - c128.clone() - one.clone())
                * (one.clone() + one.clone()))
                * is_c1.clone()
                + ((s_bytes0 - c128.clone()) * (one.clone() + one.clone()) - one.clone())
                    * is_c16.clone();
            let leaf_nibbles_short = ((s_rlp2.clone() - c128.clone() - one.clone())
                * (one.clone() + one.clone()))
                * is_c1
                + ((s_rlp2 - c128.clone()) * (one.clone() + one.clone()) - one.clone()) * is_c16;
            let leaf_nibbles_one_nibble = one.clone();

            let leaf_nibbles = leaf_nibbles_long * is_long
                + leaf_nibbles_short * is_short
                + leaf_nibbles_one_nibble * one_nibble;

            let nibbles_count = meta.query_advice(
                s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                Rotation(rot_into_init - BRANCH_ROWS_NUM),
            ) * (one.clone() - is_first_storage_level);

            /*
            Checking the total number of nibbles is to prevent having short addresses
            which could lead to a root node which would be shorter than 32 bytes and thus not hashed. That
            means the trie could be manipulated to reach a desired root.

            To get the number of nibbles above the leaf we need to go into the branch above the placeholder branch.

            Note that when the leaf is in the first storage level (but positioned after the placeholder
            in the circuit), there is no branch above the placeholder branch from where
            `nibbles_count` is to be retrieved. In that case `nibbles_count = 0`.
            */
            constraints.push((
                "Total number of account address nibbles is 64 (after placeholder)",
                q_enable
                    * is_branch_placeholder
                    * (one.clone() - is_leaf_in_first_level)
                    * (one.clone() - is_inserted_ext_node)
                    * (nibbles_count + leaf_nibbles - c64.clone()),
            ));

            constraints
        });

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
        getProof storage leaf examples:
            short (one RLP byte > 128: 160):
            [226,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,1]

            long (two RLP bytes: 67, 160):
            [248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,17

            last_level (one RLP byte: 32)
            32 at position 1 means there are no key nibbles (last level):
            [227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
            [194,32,1]

            this one falls into short again:
            [196,130,32,0,1]
        */

        /*
        Info whether leaf rlp is long or short:
         - long means the key length is at position 2.
         - short means the key length is at position 1.
        */
        let mut typ = "short";
        if row.get_byte(0) == 248 {
            typ = "long";
        } else if row.get_byte(1) == 32 {
            typ = "last_level";
        } else if row.get_byte(1) < 128 {
            typ = "one_nibble";
        }
        mpt_config.assign_long_short(region, typ, offset).ok();
 
        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len: usize;
        if typ == "long" {
            len = (row.get_byte(2) - 128) as usize + 3;
        } else if typ == "short" {
            len = (row.get_byte(1) - 128) as usize + 2;
        } else {
            // last_level or one_nibble
            len = 2
        }
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

        // note that this assignment needs to be after assign_acc call
        if row.get_byte(0) < 223 {
            // when shorter than 32 bytes, the node doesn't get hashed
            // not_hashed
            region
                .assign_advice(
                    || "assign not_hashed".to_string(),
                    mpt_config.accumulators.acc_c.rlc,
                    offset,
                    || Value::known(F::one()),
                )
                .ok();
        }

        // TODO: handle if branch or extension node is added
        let mut start = S_START - 1;
        if row.get_byte(0) == 248 {
            // long RLP
            start = S_START;
        }

        // For leaf S and leaf C we need to start with the same rlc.
        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::StorageLeafSKey)
            || (pv.is_branch_c_placeholder && row.get_type() == MptWitnessRowType::StorageLeafCKey)
        {
            key_rlc_new = pv.key_rlc_prev;
            key_rlc_mult_new = pv.key_rlc_mult_prev;
        }
        if typ != "last_level" && typ != "one_nibble" {
            // If in last level or having only one nibble,
            // the key RLC is already computed using the first two bytes above.
            mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);
        }
        region
            .assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(key_rlc_new),
            )
            .ok();

        // Store key_rlc into rlc2 to be later set in leaf value C row (to enable
        // lookups):
        pv.rlc2 = key_rlc_new;
    }
}
