use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation, circuit::Region,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::{FixedTableTag, MainCols, ProofTypeCols, AccumulatorCols, MPTConfig, ProofVariables},
    param::{
        HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, 
        IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, RLP_NUM, R_TABLE_LEN, S_START,
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
*/

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        not_first_level: Column<Advice>,
        s_main: MainCols,
        c_main: MainCols,
        accs: AccumulatorCols, // acc_c contains key_rlc_prev & key_rlc_mult_prev
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        address_rlc: Column<Advice>,
        sel2: Column<Advice>,
        is_s: bool,
    ) -> Self {
        let config = AccountLeafKeyConfig { _marker: PhantomData };
        let one = Expression::Constant(F::one());
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
            In each row of the account leaf we compute an intermediate RLC of the whole leaf.
            The RLC after account leaf key row is stored in `acc` column. We check the stored value
            is computed correctly.
            */
            constraints.push(("Leaf key RLC", q_enable.clone() * (expr - acc)));

            constraints
        });
 
        /*
        /*
        Key RLC is computed over `s_main.bytes[1]`, ..., `s_main.bytes[31]` because we do not know
        the key length in advance. To prevent changing the key and setting `s_main.bytes[i]` for
        `i > nonce_len + 1` to get the desired nonce RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.
        The key can also appear in `c_main.rlp1` and `c_main.rlp2`, so we need to check these two columns too.
        
        Note: the key length is always in s_main.bytes[0] here as opposed to storage
        key leaf where it can appear in s_rlp2 too. This is because the account
        leaf contains nonce, balance, ... which makes it always longer than 55 bytes,
        which makes a RLP to start with 248 (s_rlp1) and having one byte (in s_rlp2)
        for the length of the remaining stream.
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
        key_len_lookup(meta, q_enable, 32, s_main.bytes[0], c_main.rlp1, 128, fixed_table);
        key_len_lookup(meta, q_enable, 33, s_main.bytes[0], c_main.rlp2, 128, fixed_table);
        */

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
        mult_diff_lookup(meta, q_enable, 3, s_main.bytes[0], accs.acc_s.mult, 128, fixed_table);

        //  Note: there is no need to check key_rlc_mult as it is not used after this row.

        meta.create_gate(
            "Account leaf address RLC (leaf not in first level, branch not placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let mut is_branch_placeholder =
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
                if !is_s {
                    is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
                }
                let is_branch_placeholder = meta.query_advice(
                    is_branch_placeholder,
                    Rotation(rot_into_first_branch_child - 1),
                );

                let is_leaf_in_first_level =
                    one.clone() - meta.query_advice(not_first_level, Rotation::cur());
                    
                let key_rlc_acc_start =
                    meta.query_advice(accs.key.rlc, Rotation(rot_into_first_branch_child));
                let key_mult_start =
                    meta.query_advice(accs.key.mult, Rotation(rot_into_first_branch_child));

                // sel1, sel2 is in init branch
                let sel1 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let sel2 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );

                /*
                sel1/sel2 hold the information whether there is even or odd number of nibbles in the leaf.

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
                let mut key_rlc_acc = key_rlc_acc_start.clone()
                    + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();
                let mut key_mult = key_mult_start.clone() * r_table[0].clone() * sel1;
                key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If there is an even number of nibbles in the leaf, `s_main.bytes[1]` need to be 32.
                */
                constraints.push((
                    "Account leaf key with even nibbles: s_main.bytes[1] = 32",
                    q_enable.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (s_advice1 - c32)
                        * sel2,
                ));

                let s_advices2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc = key_rlc_acc + s * key_mult.clone() * r_table[ind - 3].clone();
                }

                let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                key_rlc_acc = key_rlc_acc + c_rlp1 * key_mult.clone() * r_table[29].clone();
                key_rlc_acc = key_rlc_acc + c_rlp2 * key_mult * r_table[30].clone();

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
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (key_rlc_acc.clone() - key_rlc.clone()),
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
                    q_enable
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (one.clone() - is_non_existing_account_proof.clone())
                        * (key_rlc.clone() - address_rlc.clone()),
                ));

                constraints
            },
        );

        meta.create_gate("Account leaf address RLC (leaf in first level)", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_leaf_in_first_level =
                one.clone() - meta.query_advice(not_first_level, Rotation::cur());

            let c32 = Expression::Constant(F::from(32));

            // Note: when leaf is in the first level, the key stored in the leaf is always of length 33 -
            // the first byte being 32 (when after branch, the information whether there the key is odd or even
            // is in s_main.bytes[IS_BRANCH_C16_POS - LAYOUT_OFFSET] (see sel1/sel2).

            let s_advice1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
            let mut key_rlc_acc = Expression::Constant(F::zero());

            constraints.push((
                "Account leaf key s_main.bytes[1] = 32",
                q_enable.clone() * (s_advice1 - c32) * is_leaf_in_first_level.clone(),
            ));

            let s_advices2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
            key_rlc_acc = key_rlc_acc + s_advices2;

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s * r_table[ind - 3].clone();
            }

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            key_rlc_acc = key_rlc_acc + c_rlp1 * r_table[29].clone();
            key_rlc_acc = key_rlc_acc + c_rlp2 * r_table[30].clone();

            let key_rlc = meta.query_advice(accs.key.rlc, Rotation::cur());
            let address_rlc = meta.query_advice(address_rlc, Rotation::cur());

            /*
            As above for the cases when the account is not in the first level. However, here we do not
            fetch for the intermediate RLC from the branch above as there is no branch above.
            */
            constraints.push((
                "Account address RLC",
                q_enable.clone()
                    * is_leaf_in_first_level.clone()
                    * (key_rlc_acc.clone() - key_rlc.clone()),
            ));

            let is_non_existing_account_proof =
                meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());
            constraints.push((
                "Computed account address RLC same as value in address_rlc column",
                q_enable
                * is_leaf_in_first_level.clone()
                * (one.clone() - is_non_existing_account_proof.clone())
                * (key_rlc.clone() - address_rlc.clone()),
            ));

            constraints
        });

        /*
        When there is an account leaf after a placeholder branch, the intermediate key RLC needs to be
        fetched from the branch above the placeholder branch. That would require a rotation over two
        levels which leads into ConstrainedPoisoned because we are accessing the rows before 0 in
        some cases. For this reason, we copy previous key RLC to the current branch so that we have
        in each branch a current and previous key RLC at our disposal. This way we do not need to
        rotate over two levels.
        */
        meta.create_gate("Previous level address RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // All branch children have the same not_first_level, any rotation could be
            // used.
            let is_branch_in_first_level = one.clone()
                - meta.query_advice(not_first_level, Rotation(rot_into_first_branch_child));
            let is_account_in_first_level =
                one.clone() - meta.query_advice(not_first_level, Rotation::cur());
            // If account is in the first level or the branch above the account leaf is in
            // the first level, there is no branch a level above from where the
            // key_rlc could be copied.

            // Could be used any rotation into previous branch, because key RLC is the same
            // in all branch children:
            let rot_into_prev_branch = rot_into_init - 5;
            // TODO: check why a different rotation causes (for example rot_into_init - 3)
            // causes ConstraintPoisened

            // key_rlc_mult_prev_level = 1 if no_prev_key_rlc
            let key_rlc_mult_prev_level = (one.clone() - is_branch_in_first_level.clone())
                * meta.query_advice(accs.key.mult, Rotation(rot_into_prev_branch))
                + is_branch_in_first_level.clone();
            // key_rlc_prev_level = 0 if no_prev_key_rlc
            let key_rlc_prev_level = (one.clone() - is_branch_in_first_level.clone())
                * meta.query_advice(accs.key.rlc, Rotation(rot_into_prev_branch));

            let rlc_prev = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
            let mult_prev = meta.query_advice(accs.acc_c.mult, Rotation::cur());

            /*
            We need to ensure that the key RLC from the branch above the placeholder branch is copied
            to `accs.acc_c.rlc`. This enables us to compute the address RLC after a branch placeholder
            (see the constraint below) by not using rotations over two levels (we have the intermediate
            RLC in the current row).
            */
            constraints.push((
                "Previous key RLC",
                q_enable.clone()
                    * (one.clone() - is_account_in_first_level.clone())
                    * (rlc_prev - key_rlc_prev_level),
            ));

            /*
            We need to ensure that the key RLC mult from the branch above the placeholder branch is copied
            to `accs.acc_c.mult`.
            */
            constraints.push((
                "Previous key RLC mult",
                q_enable
                    * (one.clone() - is_account_in_first_level)
                    * (mult_prev - key_rlc_mult_prev_level),
            ));

            constraints
        });

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
        meta.create_gate("Account leaf address RLC (after placeholder)", |meta| {
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
                one.clone() - meta.query_advice(not_first_level, Rotation::cur());

            let key_rlc_acc_start = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
            let key_mult_start = meta.query_advice(accs.acc_c.mult, Rotation::cur());

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

            let sel1 = (one.clone() - is_extension_node.clone()) * sel2p.clone()
                + is_ext_short_c16.clone() * sel1p.clone()
                + is_ext_short_c1.clone() * sel2p.clone()
                + is_ext_long_even_c16.clone() * sel2p.clone()
                + is_ext_long_even_c1.clone() * sel1p.clone()
                + is_ext_long_odd_c16.clone() * sel1p.clone()
                + is_ext_long_odd_c1.clone() * sel2p.clone();

            let sel2 = one.clone() - sel1.clone();

            // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
            let s_advice1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
            let mut key_rlc_acc = key_rlc_acc_start.clone()
                + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();
            let mut key_mult = key_mult_start.clone() * r_table[0].clone() * sel1;
            key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1, we have 32 in s_main.bytes[1].
            constraints.push((
                "Account leaf key acc s_advice1",
                q_enable.clone()
                    * (s_advice1 - c32)
                    * sel2
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_in_first_level.clone()),
            ));

            let s_advices2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
            key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            key_rlc_acc = key_rlc_acc + c_rlp1 * key_mult.clone() * r_table[29].clone();
            key_rlc_acc = key_rlc_acc + c_rlp2 * key_mult * r_table[30].clone();

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
                    * (key_rlc_acc.clone() - key_rlc.clone()),
            ));

            constraints
        });

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
                let is_leaf_placeholder = meta.query_advice(sel2, Rotation(rot_into_init+1));
                let is_account_delete_mod = meta.query_advice(proof_type.is_account_delete_mod, Rotation::cur());
                let is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                // Note: this constraint suffices because the proper transition from branch to a leaf (2. case)
                // is checked by constraints in account_leaf_key_in_added_branch.
                constraints.push((
                    "If account delete, there is either a placeholder leaf or a placeholder branch",
                    q_enable.clone()
                        * is_account_delete_mod.clone()
                        * (one.clone() - is_leaf_placeholder.clone())
                        * (one.clone() - is_branch_placeholder.clone()),
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
        pv: &mut ProofVariables<F>,
        row: &Vec<u8>,
        offset: usize,
    ) {
        // account leaf key S & C
        let mut acc = F::zero();
        let mut acc_mult = F::one();
        // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
        let key_len = (row[2] - 128) as usize;
        for b in row.iter().take(3 + key_len) {
            acc += F::from(*b as u64) * acc_mult;
            acc_mult *= mpt_config.acc_r;
        }
        // Assigning acc_s, acc_mult_s below together with acc_c
        // (key_rlc_prev) and acc_c_mult
        // (key_rlc_mult_prev).

        if row[row.len() - 1] == 6 {
            pv.acc_account_s = acc;
            pv.acc_mult_account_s = acc_mult
        } else {
            pv.acc_account_c = acc;
            pv.acc_mult_account_c = acc_mult
        }

        // For leaf S and leaf C we need to start with the same rlc.
        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        if (pv.is_branch_s_placeholder && row[row.len() - 1] == 6)
            || (pv.is_branch_c_placeholder && row[row.len() - 1] == 4)
        {
            key_rlc_new = pv.key_rlc_prev;
            key_rlc_mult_new = pv.key_rlc_mult_prev;
        }

        mpt_config.compute_key_rlc(row, &mut key_rlc_new, &mut key_rlc_mult_new, S_START);
        region.assign_advice(
            || "assign key_rlc".to_string(),
            mpt_config.accumulators.key.rlc,
            offset,
            || Ok(key_rlc_new),
        ).ok();

        // Assign previous key RLC and mult in acc_c and acc_c_mult - don't
        // use sel1/sel2 here (as in storage leaf case) as sel1/sel2 is
        // used for whether nonce/balance is short/long (in nonce balance
        // row, see offset - 1).
        // Constraints for previous key RLC are in account_leaf_key.
        mpt_config.assign_acc(
            region,
            acc,
            acc_mult,
            pv.key_rlc_prev,
            pv.key_rlc_mult_prev,
            offset,
        ).ok();
    }
}

