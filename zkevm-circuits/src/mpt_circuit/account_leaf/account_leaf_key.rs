use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols, ProofTypeCols},
    mpt_circuit::helpers::{compute_rlc, mult_diff_lookup, range_lookups, get_is_inserted_extension_node},
    mpt_circuit::param::{
        BRANCH_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
        IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, IS_EXT_LONG_EVEN_C16_POS,
        IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS,
        IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, NIBBLES_COUNTER_POS, POWER_OF_RANDOMNESS_LEN,
        RLP_NUM, S_START,
    },
    mpt_circuit::witness_row::{MptWitnessRow, MptWitnessRowType},
    mpt_circuit::{
        helpers::key_len_lookup, param::IS_ACCOUNT_DELETE_MOD_POS, FixedTableTag, MPTConfig,
        ProofValues,
    },
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

The constraints in this file apply to ACCOUNT_LEAF_KEY_S and ACCOUNT_LEAF_KEY_C rows.

For example, the two rows might be:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

Here, in `ACCOUNT_LEAF_KEY_S` example row, there are key nibbles for `S` proof stored in compact form.
The nibbles start at `s_main.bytes[1]` and can go to `c_main.rlp2`.

In `ACCOUNT_LEAF_KEY_C` example row, there are key nibbles for `C` proof stored in compact form.
The nibbles start at `s_main.bytes[1]` and can go to `c_main.rlp2`.

The whole account leaf looks like:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

There are two main scenarios when an account is added to the trie:
 1. There exists another account which has the same address to the some point as the one that
 is being added, including the position of this account in the branch.
 In this case a new branch is added to the trie.
 The existing account drifts down one level to the new branch. The newly
 added account will also appear in this branch. For example, let us say that we have the account `A`
 with nibbles `[3, 12, 3]` in the trie. We then add the account `A1` with nibbles `[3, 12, 5]`
 to the trie. The branch will appear (at position `[3, 12]`) which will have `A` at position 3
 and `A1` at position 5. This means there will be an additional branch in `C` proof (or in `S`
 proof when the situation is reversed - we are deleting the leaf instead of adding) and
 for this reason we add a placeholder branch for `S` proof (for `C` proof in reversed situation)
 to preserve the circuit layout (more details about this technicality are given below).

 2. The branch where the new account is to be added has nil node at the position where the new account
 is to be added. For example, let us have a branch at `[3, 12]`, we are adding a leaf with the
 first three nibbles as `[3, 12, 5]`, and the position 5 in our branch is not occupied.
 There does not exist an account which has the same address to the some point.
 In this case, the `getProof` response does not end with a leaf, but with a branch.
 To preserve the layout, a placeholder account leaf is added.

Lookups:
The `is_account_delete_mod` lookup is enabled in `ACCOUNT_LEAF_KEY_S` row.
*/

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        position_cols: PositionCols<F>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        address_rlc: Column<Advice>,
        sel2: Column<Advice>,
        is_s: bool,
        check_zeros: bool,
    ) -> Self {
        let config = AccountLeafKeyConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());
        let c64 = Expression::Constant(F::from(64));
        let c128 = Expression::Constant(F::from(128));
        // key rlc is in the first branch node
        let mut rot_into_first_branch_child = -18;
        if !is_s {
            rot_into_first_branch_child = -19;
        }
        let rot_into_init = rot_into_first_branch_child - 1;

        meta.create_gate("Account leaf RLC after key", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            /*
            [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
            There are 112 bytes after the first two bytes.
            157 means the key is 29 (157 - 128) bytes long.
            */

            let c248 = Expression::Constant(F::from(248));

            let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());

            /*
            Account leaf always starts with 248 because its length is always longer than 55 bytes due to
            containing two hashes - storage root and codehash, which are both of 32 bytes.
            248 is RLP byte which means there is `1 = 248 - 247` byte specifying the length of the remaining
            list. For example, in [248,112,157,59,...], there are 112 byte after the second byte.
            */
            constraints.push((
                "Account leaf key s_main.rlp1 = 248",
                q_enable.clone() * (s_rlp1.clone() - c248),
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
            In each row of the account leaf we compute an intermediate RLC of the whole leaf.
            The RLC after account leaf key row is stored in `acc` column. We check the stored value
            is computed correctly.
            */
            constraints.push(("Leaf key RLC", q_enable * (expr - acc)));

            constraints
        });

        /*
        Key RLC is computed over all of `s_main.bytes[1], ..., s_main.bytes[31], c_main.rlp1, c_main.rlp2`
        because we do not know the key length in advance.
        To prevent changing the key and setting `s_main.bytes[i]` (or `c_main.rlp1/c_main.rlp2`) for
        `i > key_len + 1` to get the desired key RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.

        Note: the key length is always in s_main.bytes[0] here as opposed to storage
        key leaf where it can appear in s_rlp2 too. This is because the account
        leaf contains nonce, balance, ... which makes it always longer than 55 bytes,
        which makes a RLP to start with 248 (s_rlp1) and having one byte (in s_rlp2)
        for the length of the remaining stream.
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
                q_enable,
                32,
                s_main.bytes[0],
                c_main.rlp1,
                128,
                fixed_table,
            );
            key_len_lookup(
                meta,
                q_enable,
                33,
                s_main.bytes[0],
                c_main.rlp2,
                128,
                fixed_table,
            );
        }

        /*
        When the account intermediate RLC is computed in the next row (nonce balance row), we need
        to know the intermediate RLC from the current row and the randomness multiplier (`r` to some power).
        The power of randomness `r` is determined by the key length - the intermediate RLC in the current row
        is computed as (key starts in `s_main.bytes[1]`):
        `rlc = s_main.rlp1 + s_main.rlp2 * r + s_main.bytes[0] * r^2 + key_bytes[0] * r^3 + ... + key_bytes[key_len-1] * r^{key_len + 2}`
        So the multiplier to be used in the next row is `r^{key_len + 2}`.

        `mult_diff` needs to correspond to the key length + 2 RLP bytes + 1 byte for byte that contains the key length.
        That means `mult_diff` needs to be `r^{key_len+1}` where `key_len = s_main.bytes[0] - 128`.
        */
        mult_diff_lookup(
            meta,
            q_enable,
            3,
            s_main.bytes[0],
            accs.acc_s.mult,
            128,
            fixed_table,
        );

        // Note: there is no need to check `key_rlc_mult` as it is not used after this
        // row.

        meta.create_gate(
            "Account leaf address RLC & nibbles count (branch not placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let is_leaf_in_first_level =
                    one.clone() - meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let mut is_branch_placeholder =
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
                if !is_s {
                    is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
                }
                let mut is_branch_placeholder = meta.query_advice(
                    is_branch_placeholder,
                    Rotation(rot_into_first_branch_child - 1),
                );

                // `is_branch_placeholder = 0` when in first level
                is_branch_placeholder = is_branch_placeholder.clone() * (one.clone() - is_leaf_in_first_level.clone());

                let mut key_rlc_acc_start =
                    meta.query_advice(accs.key.rlc, Rotation(rot_into_first_branch_child));
                let mut key_mult_start =
                    meta.query_advice(accs.key.mult, Rotation(rot_into_first_branch_child));

                /*
                `key_rlc_acc_start = 0` if leaf in first level
                `key_mult_start = 1` if leaf in first level
                */
                key_rlc_acc_start = key_rlc_acc_start.clone() * (one.clone() - is_leaf_in_first_level.clone());
                key_mult_start = key_mult_start.clone() * (one.clone() - is_leaf_in_first_level.clone()) + is_leaf_in_first_level.clone();

                let mut is_c16 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let mut is_c1 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );

                /*
                `is_c16 = 0, is_c1 = 1` if leaf in first level, because we do not have the branch above
                and we need to multiply the first nibble by 16 (as it would be `c1` in the branch above)
                */
                is_c16 = is_c16.clone() * (one.clone() - is_leaf_in_first_level.clone());
                is_c1 = is_c1.clone() * (one.clone() - is_leaf_in_first_level.clone()) + is_leaf_in_first_level.clone();

                /*
                `is_c16`/`is_c1` hold the information whether there is even or odd number of nibbles in the leaf.

                Let us observe a case with even number of nibbles first:
                `[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]`
                In this case we have 32 in `s_main.bytes[1]`. The nibbles start in `s_main.bytes[2]`,
                eacy byte presents two nibbles. We can simply add the bytes to the intermediate RLC:
                `rlc = intermediate_rlc + s_main.bytes[2] * mult_prev + s_main.bytes[3] * mult_prev * r + ... `

                Let us observe a case with odd number of nibbles now:
                `[248,106,161,51,25,...]`
                In this case we have 51 in `s_main.bytes[1]`, this presents the first nibble: `3 = 51 - 48`.
                From `s_main.bytes[2]` it is as in the even number case. We compute the RLC as:
                `rlc = intermediate_rlc + (s_main.bytes[1] - 48) * mult_prev + s_main.bytes[2] * mult_prev * r + ... `
                */

                let c32 = Expression::Constant(F::from(32));
                let c48 = Expression::Constant(F::from(48));

                // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
                let s_advice1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                let mut key_rlc_acc = key_rlc_acc_start
                    + (s_advice1.clone() - c48) * key_mult_start.clone() * is_c16.clone();
                let mut key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16.clone();
                key_mult = key_mult + key_mult_start * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If there is an even number of nibbles in the leaf, `s_main.bytes[1]` need to be 32.
                */
                constraints.push((
                    "Account leaf key with even nibbles: s_main.bytes[1] = 32",
                    q_enable.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * (s_advice1 - c32)
                        * is_c1.clone(),
                ));

                let s_advices2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc = key_rlc_acc + s * key_mult.clone() * power_of_randomness[ind - 3].clone();
                }

                let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                key_rlc_acc = key_rlc_acc + c_rlp1 * key_mult.clone() * power_of_randomness[29].clone();
                key_rlc_acc = key_rlc_acc + c_rlp2 * key_mult * power_of_randomness[30].clone();

                let key_rlc = meta.query_advice(accs.key.rlc, Rotation::cur());
                let address_rlc = meta.query_advice(address_rlc, Rotation::cur());

                /*
                Account leaf contains the remaining nibbles of the account address. Combining the path 
                of the leaf in the trie and these remaining nibbles needs to be the same as the account
                address which is given in the `address_rlc` column that is to be used by a lookup (see the
                constraint below).

                Address RLC needs to be computed properly - we need to take into account the path of the leaf 
                in the trie and the remaining nibbles in the account leaf.

                The intermediate RLC is retrieved from the last branch above the account leaf - this
                presents the RLC after the path to the leaf is considered. After this, the bytes (nibbles
                in a compacted form) in the leaf have to be added to the RLC.
                */
                constraints.push((
                    "Account address RLC",
                    q_enable.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * (key_rlc_acc - key_rlc.clone()),
                ));

                let is_non_existing_account_proof =
                    meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());

                /*
                The computed key RLC needs to be the same as the value in `address_rlc` column.
                This seems to be redundant (we could write one constraint instead of two:
                `key_rlc_acc - address_rlc = 0`), but note that `key_rlc` is used in
                `account_leaf_key_in_added_branch` and in cases when there is a placeholder branch
                we have `key_rlc - address_rlc != 0` because `key_rlc` is computed for the branch
                that is parallel to the placeholder branch.
                */
                constraints.push((
                    "Computed account address RLC same as value in address_rlc column",
                    q_enable.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_non_existing_account_proof)
                        * (key_rlc - address_rlc),
                ));

                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                let leaf_nibbles = ((s_bytes0.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone())) * is_c1 +
                    ((s_bytes0 - c128.clone()) * (one.clone() + one.clone()) - one.clone()) * is_c16;

                let mut nibbles_count = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                // nibbles_count = 0 if in first storage level
                nibbles_count = nibbles_count.clone() * (one.clone() - is_leaf_in_first_level);

                /* 
                Checking the total number of nibbles is to prevent having short addresses
                which could lead to a root node which would be shorter than 32 bytes and thus not hashed. That
                means the trie could be manipulated to reach a desired root.
                */
                constraints.push((
                    "Total number of account address nibbles is 64 (not first level, not branch placeholder)",
                    q_enable
                        * (one.clone() - is_branch_placeholder)
                        // Note: we need to check the number of nibbles being 64 for non_existing_account_proof too
                        // (even if the address being checked here might is the address of the wrong leaf)
                        * (nibbles_count + leaf_nibbles - c64.clone()),
                ));

                constraints
            },
        );

        /*
        The example layout for a branch placeholder looks like (placeholder could be in `C` proof too):
            Branch 1S               || Branch 1C
            Branch 2S (placeholder) || Branch 2C
            Leaf S
            Leaf C

        Using `Previous key RLC` constraint we ensured that we copied the key RLC from Branch 1S
        to Leaf S `accs.acc_c.rlc` column. So when add nibbles to compute the key RLC (address RLC)
        of the account, we start with `accs.acc_c.rlc` value from the current row.
        */
        meta.create_gate(
            "Account leaf address RLC & nibbles count (after placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let mut is_branch_placeholder = s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
                if !is_s {
                    is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
                }
                let is_branch_placeholder = meta.query_advice(
                    is_branch_placeholder,
                    Rotation(rot_into_first_branch_child - 1),
                );

                let is_leaf_in_first_level =
                    one.clone() - meta.query_advice(position_cols.not_first_level, Rotation::cur());

                // let key_rlc_acc_start = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                // let key_mult_start = meta.query_advice(accs.acc_c.mult, Rotation::cur());

                let is_placeholder_branch_in_first_level = one.clone()
                    - meta.query_advice(position_cols.not_first_level, Rotation(rot_into_init));

                // Note: key RLC is in the first branch node (not branch init).
                let rot_level_above = rot_into_init + 1 - BRANCH_ROWS_NUM;

                let key_rlc_acc_start = meta.query_advice(accs.key.rlc, Rotation(rot_level_above))
                    * (one.clone() - is_placeholder_branch_in_first_level.clone());
                let key_mult_start = meta.query_advice(accs.key.mult, Rotation(rot_level_above))
                    * (one.clone() - is_placeholder_branch_in_first_level.clone())
                    + is_placeholder_branch_in_first_level;

                // TODO: the expressions below can be simplified

                let sel1p = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let sel2p = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );

                let c32 = Expression::Constant(F::from(32));
                let c48 = Expression::Constant(F::from(48));

                /*
                sel1/sel2 tells us whether there is an even or odd number of nibbles in the leaf.
                sel1/sel2 info is need for the computation of the key RLC (see below), in case of a leaf
                after branch placeholder, sel1/sel2 can be computed as follows.

                Note that we cannot rotate back into Branch 1S because we get PoisonedConstraint
                in extension_node_key.

                Instead, we can rotate into branch parallel to the placeholder branch and compute sel1/sel2 with info from there.
                Let's denote sel1/sel2 from this branch by sel1p/sel2p.

                There are a couple of different cases, for example when branch/extension node parallel
                to the placeholder branch is a regular branch.
                There is only one nibble taken by Branch 2C, so sel1/sel2 simply turns around compared to sel1p/sel2p:
                sel1 = sel2p
                sel2 = sel1p

                When branch/extension node parallel to the placeholder branch is an extension node, it depends on the
                number of nibbles. If there is an odd number of nibbles: sel1 = sel1p, sel2 = sel2p. If there is
                an even number of nibbles, it turns around.

                Note: _c16 presents the same info as sel1, _c1 presents the same info as sel2 (this information is doubled
                to reduce the degree when handling different cases in extension_node_key).
                */

                let is_ext_short_c16 = meta.query_advice(
                    s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_short_c1 = meta.query_advice(
                    s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_even_c16 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_even_c1 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_odd_c16 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_odd_c1 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                let is_extension_node = is_ext_short_c16.clone()
                    + is_ext_short_c1.clone()
                    + is_ext_long_even_c16.clone()
                    + is_ext_long_even_c1.clone()
                    + is_ext_long_odd_c16.clone()
                    + is_ext_long_odd_c1.clone();

                let sel1 = (one.clone() - is_extension_node) * sel2p.clone()
                    + is_ext_short_c16 * sel1p.clone()
                    + is_ext_short_c1 * sel2p.clone()
                    + is_ext_long_even_c16 * sel2p.clone()
                    + is_ext_long_even_c1 * sel1p.clone()
                    + is_ext_long_odd_c16 * sel1p
                    + is_ext_long_odd_c1 * sel2p;

                let sel2 = one.clone() - sel1.clone();

                /*
                When extension node is inserted, the leaf is only a placeholder (as well as branch) -
                we need to compare the hash of the extension node in the inserted extension node row
                to the hash in the branch above the placeholder branch
                (see `extension_node_inserted.rs`).
                */
                let is_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_init, is_s);

                // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
                let s_advice1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                let mut key_rlc_acc = key_rlc_acc_start
                    + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();
                let mut key_mult =
                    key_mult_start.clone() * power_of_randomness[0].clone() * sel1.clone();
                key_mult = key_mult + key_mult_start * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                // If sel2 = 1, we have 32 in s_main.bytes[1].
                constraints.push((
                    "Account leaf key acc s_advice1",
                    q_enable.clone()
                        * (s_advice1 - c32)
                        * sel2.clone()
                        * is_branch_placeholder.clone()
                        * (one.clone() - is_inserted_ext_node.clone())
                        * (one.clone() - is_leaf_in_first_level.clone()),
                ));

                let s_advices2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc =
                        key_rlc_acc + s * key_mult.clone() * power_of_randomness[ind - 3].clone();
                }

                let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                key_rlc_acc =
                    key_rlc_acc + c_rlp1 * key_mult.clone() * power_of_randomness[29].clone();
                key_rlc_acc = key_rlc_acc + c_rlp2 * key_mult * power_of_randomness[30].clone();

                let key_rlc = meta.query_advice(accs.key.rlc, Rotation::cur());

                /*
                Although `key_rlc` is not compared to `address_rlc` in the case when the leaf
                is below the placeholder branch (`address_rlc` is compared to the parallel leaf `key_rlc`),
                we still need properly computed `key_rlc` to reuse it in `account_leaf_key_in_added_branch`.

                Note: `key_rlc - address_rlc != 0` when placeholder branch.
                */
                constraints.push((
                    "Account address RLC after branch placeholder",
                    q_enable.clone()
                        * is_branch_placeholder.clone()
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (one.clone() - is_inserted_ext_node.clone())
                        * (key_rlc_acc - key_rlc),
                ));

                let s_advice0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                let leaf_nibbles = ((s_advice0.clone() - c128.clone() - one.clone())
                    * (one.clone() + one.clone()))
                    * sel2
                    + ((s_advice0 - c128.clone()) * (one.clone() + one.clone()) - one.clone())
                        * sel1;

                let is_branch_in_first_level = one.clone()
                    - meta.query_advice(
                        position_cols.not_first_level,
                        Rotation(rot_into_first_branch_child),
                    );

                /*
                Note that when the leaf is in the first level (but positioned after the placeholder
                in the circuit), there is no branch above the placeholder branch from where
                `nibbles_count` is to be retrieved. In that case `nibbles_count = 0`.
                */
                let nibbles_count = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_init - BRANCH_ROWS_NUM),
                ) * (one.clone() - is_branch_in_first_level);

                constraints.push((
                    "Total number of account address nibbles is 64 (after placeholder)",
                    q_enable
                        * is_branch_placeholder
                        * (one.clone() - is_leaf_in_first_level)
                        * (one.clone() - is_inserted_ext_node.clone())
                        * (nibbles_count + leaf_nibbles - c64.clone()),
                ));

                constraints
            },
        );

        if !is_s {
            meta.create_gate("Account delete", |meta| {
                /*
                We need to make sure there is no leaf when account is deleted. Two possible cases:
                1. Account leaf is deleted and there is a nil object in branch. In this case we have
                   a placeholder leaf.
                2. Account leaf is deleted from a branch with two leaves, the remaining leaf moves one level up
                   and replaces the branch. In this case we have a branch placeholder.

                So we need to check there is a placeholder branch when we have the second case.

                Note: we do not need to cover the case when the (only) branch dissapears and only one
                leaf remains in the trie because there will always be at least two leaves
                (the genesis account) when account will be deleted,
                so there will always be a branch / extension node (and thus placeholder branch).
                */
                let mut constraints = vec![];
                let q_enable = q_enable(meta);
                // is_leaf_placeholder is stored in branch children: sel1 for S, sel2 for C.
                let is_leaf_placeholder = meta.query_advice(sel2, Rotation(rot_into_init + 1));
                let is_account_delete_mod =
                    meta.query_advice(proof_type.is_account_delete_mod, Rotation::cur());
                let is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                // Note: this constraint suffices because the proper transition from branch to a
                // leaf (2. case) is checked by constraints in
                // account_leaf_key_in_added_branch.
                constraints.push((
                    "If account delete, there is either a placeholder leaf or a placeholder branch",
                    q_enable
                        * is_account_delete_mod
                        * (one.clone() - is_leaf_placeholder)
                        * (one.clone() - is_branch_placeholder),
                ));

                constraints
            });
        }

        /*
        Range lookups ensure that `s_main`, `c_main.rlp1`, `c_main.rlp2` columns are all bytes (between 0 - 255).
        Note that `c_main.bytes` columns are not used.
        */
        range_lookups(
            meta,
            q_enable,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // s_rlp1 is always 248 (checked above)
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp2, c_main.rlp1, c_main.rlp2].to_vec(),
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
        // account leaf key S & C
        let mut acc = F::zero();
        let mut acc_mult = F::one();
        // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
        let key_len = (row.get_byte(2) - 128) as usize;
        for b in row.bytes.iter().take(3 + key_len) {
            acc += F::from(*b as u64) * acc_mult;
            acc_mult *= mpt_config.randomness;
        }

        if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
            pv.acc_account_s = acc;
            pv.acc_mult_account_s = acc_mult;

            if row.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) == 1 {
                region
                    .assign_advice(
                        || "assign lookup enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(5_u64)), /* account delete mod lookup enabled in
                                                          * this row if it is is_account_delete
                                                          * proof */
                    )
                    .ok();
            }
        } else {
            pv.acc_account_c = acc;
            pv.acc_mult_account_c = acc_mult;
        }

        // For leaf S and leaf C we need to start with the same rlc.
        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::AccountLeafKeyS)
            || (pv.is_branch_c_placeholder && row.get_type() == MptWitnessRowType::AccountLeafKeyC)
        {
            key_rlc_new = pv.key_rlc_prev;
            key_rlc_mult_new = pv.key_rlc_mult_prev;
        }

        mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, S_START);
        region
            .assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(key_rlc_new),
            )
            .ok();

        mpt_config
            .assign_acc(region, acc, acc_mult, F::zero(), F::zero(), offset)
            .ok();
    }
}
