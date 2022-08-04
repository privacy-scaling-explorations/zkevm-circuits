use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, get_bool_constraint, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::{FixedTableTag, MainCols, ProofTypeCols},
    param::{
        ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND,
        ACCOUNT_LEAF_NONCE_BALANCE_S_IND, HASH_WIDTH, ACCOUNT_NON_EXISTING_IND,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafNonceBalanceConfig {}

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

This chip applies to ACCOUNT_LEAF_NONCE_BALANCE_S and ACCOUNT_LEAF_NONCE_BALANCE_C rows.

For example, the two rows might be:
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

In `ACCOUNT_LEAF_NONCE_BALANCE_S` example row, there is `S` nonce stored in `s_main` and `S` balance in
`c_main`. We can see nonce in `S` proof is `0 = 128 - 128`.

In `ACCOUNT_LEAF_NONCE_BALANCE_C` example row, there is `C` nonce stored in `s_main` and `C` balance in
`c_main`. We can see nonce in `C` proof is `1`.

*/
pub(crate) struct AccountLeafNonceBalanceChip<F> {
    config: AccountLeafNonceBalanceConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafNonceBalanceChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_main: MainCols,
        c_main: MainCols,
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_mult_c: Column<Advice>,
        mult_diff_nonce: Column<Advice>,
        mult_diff_balance: Column<Advice>,
        r_table: Vec<Expression<F>>,
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        is_s: bool,
    ) -> AccountLeafNonceBalanceConfig {
        let config = AccountLeafNonceBalanceConfig {};
        let one = Expression::Constant(F::one());
        let c128 = Expression::Constant(F::from(128));

        meta.create_gate("Account leaf nonce balance RLC & RLP", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            /*
            [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
            There are 112 bytes after the first two bytes.
            157 means the key is 29 (157 - 128) bytes long.
            */

            // Nonce, balance, storage, codehash are string in RLP: s_rlp1 and s_rlp2
            // contains the length of this string, for example 184 80 means the second
            // part is of length 1 (183 + 1 = 184) and there are 80 bytes in this string.
            // Then there is a list rlp meta data 248 78 where (this is stored in c_rlp1 and
            // c_rlp2) 78 = 3 (nonce) + 9 (balance) + 33 (storage) + 33
            // (codehash). We have nonce in s_main.bytes and balance in c_main.bytes.
            // s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes  c_main.bytes
            // 184     80      248     78      nonce      balance

            let mut rot = -(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND);
            let mut rot_into_non_existing = -(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_NON_EXISTING_IND);
            if !is_s {
                rot = -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND);
                rot_into_non_existing = -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_NON_EXISTING_IND);
            }
            let c248 = Expression::Constant(F::from(248));

            let acc_prev = meta.query_advice(acc_s, Rotation(rot));
            let acc_mult_prev = meta.query_advice(acc_mult_s, Rotation(rot));

            let acc_mult_after_nonce = meta.query_advice(acc_mult_c, Rotation::cur());
            let mult_diff_nonce = meta.query_advice(mult_diff_nonce, Rotation::cur());
            let mult_diff_balance = meta.query_advice(mult_diff_balance, Rotation::cur());

            let is_nonce_long = meta.query_advice(
                sel1,
                Rotation(rot),
            );
            let is_balance_long = meta.query_advice(
                sel2,
                Rotation(rot),
            );

            /*
            If nonce (same holds for balance) is smaller or equal to 128, then it will occupy only one byte:
            `s_main.bytes[0]` (`c_main.bytes[0]` for balance).
            For example, the row [184,70,128,0,...,0] holds 128 in bytes[0] which means nonce = 128 - 128 = 0.
            For example, the row [184,70,1,0,...,0] holds 1 in bytes[0] which means nonce = 1.

            In case nonce (same for balance) is bigger than 128, it will occupy more than 1 byte.
            The example row below shows nonce value 142, while 129 means there is a nonce of byte
            length `1 = 129 - 128`.
            Balance in the example row below is: 28 + 5 * 256 + 107 * 256^2 + ... + 59 * 256^6, while
            135 means there are 7 = 135 - 128 bytes.
            ```
            [rlp1 rlp2 bytes[0] bytes[1]]           rlp1 rlp2 bytes[0] bytes[1]   ...    ]
            [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]

            The `sel1` column in the `ACCOUNT_LEAF_KEY_S` or `ACCOUNT_LEAF_KEY_C` row
            is used to mark whether nonce is of 1 byte (short) or more than 1 byte (long).
            `sel1 = 1` means long, `sel1 = 0` means short.
            `Bool check is_nonce_long` constraint ensures the `sel1` value is boolean.

            Analogously, `sel2` holds the information whether balance is long or short.
            `Bool check is_balance_long` constraint ensures the `sel2` value is boolean.
            */
            constraints.push((
                "Bool check is_nonce_long",
                get_bool_constraint(q_enable.clone(), is_nonce_long.clone()),
            ));
            constraints.push((
                "Bool check is_balance_long",
                get_bool_constraint(q_enable.clone(), is_balance_long.clone()),
            ));

            /*
            It is important that there are 0s in `s_main.bytes` after the nonce bytes end.
            When nonce is short (1 byte), like in `[184,70,1,0,...]`, the constraint is simple:
            `s_main.bytes[i] = 0` for all `i > 0`.

            When nonce is long, the constraints need to be written differently because we do not
            know the length of nonce in advance.
            The row below holds nonce length specification in `s_main.bytes[0]`.
            The length in the example below is `1 = 129 - 128`,
            so the constraint needs to be `s_main.bytes[i] = 0` for
            all `i > 1` (note that the actual value is in `s_main.bytes[1]`).

            ```
            [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
            ```

            But instead of 129 we could have 130 or some other value in `s_main.bytes[0]`. For this
            reason, the constraints are implemented using `key_len_lookup` (see below).
            */
            for ind in 1..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                let c = meta.query_advice(c_main.bytes[ind], Rotation::cur());
                constraints.push((
                    "s_main.bytes[i] = 0 for i > 0 when is_nonce_short",
                    q_enable.clone() * (one.clone() - is_nonce_long.clone()) * s.clone(),
                ));
                constraints.push((
                    "c_main.bytes[i] = 0 for i > 0 when is_balance_short",
                    q_enable.clone() * (one.clone() - is_balance_long.clone()) * c.clone(),
                ));
            }

            let key_len = meta.query_advice(s_main.bytes[0], Rotation(rot)) - c128.clone();
            let s_advices0_cur = meta.query_advice(s_main.bytes[0], Rotation::cur());
            let s_advices1_cur = meta.query_advice(s_main.bytes[1], Rotation::cur());

            /*
            When `non_existing_account_proof` proof type (which can be of two subtypes: with wrong leaf
            and without wrong leaf, more about it below), the `is_wrong_leaf` flag specifies whether
            the subtype is with wrong leaf or not.
            When `non_existing_account_proof` without wrong leaf
            the proof contains only branches and a placeholder account leaf.
            In this case, it is checked that there is nil in the parent branch
            at the proper position (see `account_non_existing`). Note that we need (placeholder) account
            leaf for lookups and to know when to check that parent branch has a nil.

            In `is_wrong_leaf is bool` we only check that `is_wrong_leaf` is a boolean values.
            Other wrong leaf related constraints are in other gates.
            */
            let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation(rot_into_non_existing));
            let is_non_existing_account_proof = meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());
            constraints.push((
                "is_wrong_leaf is bool",
                get_bool_constraint(q_enable.clone(), is_wrong_leaf.clone()),
            ));

            // Note: some is_wrong_leaf constraints are in this chip because account_non_existing chip
            // only triggers constraints for non_existing_account proof (see q_enable).
            constraints.push((
                "is_wrong_leaf needs to be 0 when not in non_existing_account proof",
                q_enable.clone()
                    * (one.clone() - is_non_existing_account_proof.clone())
                    * is_wrong_leaf.clone(),
            ));

            // Note: (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
            // cannot be 0 when is_non_existing_account_proof = 0.
            let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());
            let rlp_len = meta.query_advice(s_main.rlp2, Rotation(rot));
            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());

            let mut expr = acc_prev + s_rlp1.clone() * acc_mult_prev.clone();
            let mut rind = 0;
            expr = expr + s_rlp2.clone() * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;

            let c_rlp1 = meta.query_advice(c_main.rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            
            expr = expr + c_rlp1.clone() * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;
            expr = expr + c_rlp2.clone() * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;

            let nonce_value_long_rlc = s_advices1_cur.clone()
                + compute_rlc(
                    meta,
                    s_main.bytes.iter().skip(2).map(|v| *v).collect_vec(),
                    0,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            let nonce_rlc = (s_advices0_cur.clone() + nonce_value_long_rlc.clone() * r_table[0].clone()) * is_nonce_long.clone()
                + s_advices0_cur.clone() * (one.clone() - is_nonce_long.clone());

            let nonce_stored = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            /*
            Besides having nonce (its bytes) stored in `s_main.bytes`, we also have the RLC
            of nonce bytes stored in `s_mod_node_hash_rlc` column. The value in this column
            is to be used by lookups.
            This constraint ensures the RLC of a nonce is computed properly when nonce is long.
            */
            constraints.push((
                "Nonce RLC long",
                q_enable.clone() * is_nonce_long.clone() * (nonce_value_long_rlc.clone() - nonce_stored.clone()),
            ));

            /*
            Similarly as in `Nonce RLP long` constraint, this constraint ensures the RLC of a nonce
            is computed properly when nonce is short.
            */
            constraints.push((
                "Nonce RLC short",
                q_enable.clone() * (one.clone() - is_nonce_long.clone()) * (s_advices0_cur.clone() - nonce_stored.clone()),
            ));

            expr = expr + nonce_rlc * r_table[rind].clone() * acc_mult_prev.clone();

            let c_advices0_cur = meta.query_advice(c_main.bytes[0], Rotation::cur());
            let c_advices1_cur = meta.query_advice(c_main.bytes[1], Rotation::cur());
            let balance_stored = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            let balance_value_long_rlc = c_advices1_cur.clone()
                + compute_rlc(
                    meta,
                    c_main.bytes.iter().skip(2).map(|v| *v).collect_vec(),
                    0,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            let balance_rlc = (c_advices0_cur.clone() + balance_value_long_rlc.clone() * r_table[0].clone()) * is_balance_long.clone()
                + c_advices0_cur.clone() * (one.clone() - is_balance_long.clone());

            /*
            Besides having balance (its bytes) stored in `c_main.bytes`, we also have the RLC
            of nonce bytes stored in `c_mod_node_hash_rlc` column. The value in this column
            is to be used by lookups.
            `Balance RLP long` constraint ensures the RLC of a balance is computed properly when
            balance is long.
            */
            constraints.push((
                "balance RLC long",
                q_enable.clone() * is_balance_long.clone() * (balance_value_long_rlc.clone() - balance_stored.clone()),
            ));

            /*
            Similarly as in `Balance RLP long` constraint, 
            `Balance RLP short` constraint ensures the RLC of a balance is computed properly when
            balance is short.
            */
            constraints.push((
                "balance RLC short",
                q_enable.clone() * (one.clone() - is_balance_long.clone()) * (c_advices0_cur.clone() - balance_stored.clone()),
            ));

            if !is_s {
                let nonce_s_from_prev = meta.query_advice(s_mod_node_hash_rlc, Rotation::prev());
                let nonce_s_from_cur = meta.query_advice(sel1, Rotation::cur());
                let balance_s_from_prev = meta.query_advice(c_mod_node_hash_rlc, Rotation::prev());
                let balance_s_from_cur = meta.query_advice(sel2, Rotation::cur());

                // Note: when nonce or balance is 0, the actual value in the RLP encoding is 128!
                // TODO: when finalizing lookups, having 128 instead of 0 needs to be taken into account.

                /*
                To enable lookup for nonce modification we need to have S nonce and C nonce in the same row.
                For this reason, S nonce RLC is copied to `sel1` column in C row.
                */
                constraints.push((
                    "S nonce RLC is correctly copied to C row",
                    q_enable.clone() * (nonce_s_from_prev.clone() - nonce_s_from_cur.clone()),
                ));

                /*
                To enable lookup for balance modification we need to have S balance and C balance in the same row.
                For this reason, S balance RLC is copied to `sel2` column in C row.
                */
                constraints.push((
                    "S balance RLC is correctly copied to C row",
                    q_enable.clone() * (balance_s_from_prev.clone() - balance_s_from_cur.clone()),
                ));

                // Check there is only one modification at once:
                let is_storage_mod = meta.query_advice(proof_type.is_storage_mod, Rotation::cur());
                let is_nonce_mod = meta.query_advice(proof_type.is_nonce_mod, Rotation::cur());
                let is_balance_mod = meta.query_advice(proof_type.is_balance_mod, Rotation::cur());
                let is_account_delete_mod = meta.query_advice(proof_type.is_account_delete_mod, Rotation::cur());

                /*
                We need to ensure there is only one modification at a time. If there is storage or
                balance modification, we need to ensure `S` nonce and `C` nonce are the same.
                */
                constraints.push((
                    "If storage or balance modification: S nonce = C nonce",
                    q_enable.clone()
                        * (is_storage_mod.clone()
                            + is_balance_mod.clone())
                        * (one.clone() - is_account_delete_mod.clone())
                        * (nonce_s_from_cur.clone() - nonce_stored.clone()),
                ));

                /*
                We need to ensure there is only one modification at a time. If there is storage or
                nonce modification, we need to ensure `S` balance and `C` balance are the same.
                */
                constraints.push((
                    "If storage or nonce modification: S balance = C balance",
                    q_enable.clone()
                        * (is_storage_mod.clone() + is_nonce_mod.clone())
                        * (one.clone() - is_account_delete_mod.clone())
                        * (balance_s_from_cur.clone() - balance_stored.clone()),
                ));
            }

            expr = expr + balance_rlc * acc_mult_after_nonce.clone();

            let acc = meta.query_advice(acc_s, Rotation::cur());
            constraints.push(("leaf nonce balance acc", q_enable.clone() * (expr - acc)));

            let acc_mult_final = meta.query_advice(acc_mult_s, Rotation::cur());

            /*
            When adding nonce bytes to the account leaf RLC we do:
            `rlc_after_nonce = rlc_tmp + s_main.bytes[0] * mult_tmp + s_main.bytes[1] * mult_tmp * r
                + ... + s_main.bytes[k] * mult_tmp * r^k`
            Note that `rlc_tmp` means the RLC after the previous row, while `mult_tmp` means the multiplier
            (power of randomness `r`) that needs to be used for the first byte in the current row.

            In this case we assumed there are `k + 1` nonce bytes. After this we continue adding bytes:
            `rlc_after_nonce + b1 * mult_tmp * r^{k+1} + b2 * mult_tmp * r^{k+1} * r + ...
            Note that `b1` and `b2` are the first two bytes that need to used next (balance bytes).

            The problem is `k` can be different from case to case. For this reason, we store `r^{k+1}` in
            `mult_diff_nonce` (which is actually `acc_c`).
            That means we can compute the expression above as:
            `rlc_after_nonce + b1 * mult_tmp * mult_diff_nonce + b2 * mult_tmp * mult_diff_nonce * r + ...

            However, we need to ensure that `mult_diff_nonce` corresponds to `s_main.bytes[0]` where the length
            of the nonce is specified. This is done using `key_len_lookup` below.

            There is one more detail: when computing RLC after nonce, we compute also the bytes that come before
            nonce bytes in the row. These are: `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`.
            It is a bit confusing (we are limited with layout), but `c_main.rlp1` and `c_main.rlp2`
            are bytes that actually appear in the account leaf RLP stream before `s_main.bytes`.
            So we have:
            `rlc_after_nonce = rlc_tmp + s_main.rlp1 * mult_tmp + s_main.rlp2 * mult_tmp * r
                + c_main.rlp1 * mult_tmp * r^2 + c_main.rlp2 * mult_tmp * r^3 + s_main.bytes[0] * mult_tmp * r^4 + ...
                + s_main.bytes[k] * mult_tmp * r^4 * r^k`
            That means `mult_diff_nonce` needs to store `r^4 * r^{k+1}` and we continue computing the RLC
            as mentioned above:
            `rlc_after_nonce + b1 * mult_tmp * mult_diff_nonce + b2 * mult_tmp * mult_diff_nonce * r + ...

            Let us observe the following example.
            [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
            Here:
            `rlc_after_nonce = rlc_tmp + 184 * mult_tmp + 78 * mult_tmp * r + 248 * mult_tmp * r^2
                + 76 * mult_tmp * r^3 + 129 * mult_tmp * r^4 + 142 * mult_tmp * r^5`
            And we continue computing the RLC:
            `rlc_after_nonce + 135 * mult_tmp * mult_diff_nonce + 28 + mult_tmp * mult_diff_nonce * r + ... `
            */
            constraints.push((
                "Leaf nonce acc mult (nonce long)",
                q_enable.clone()
                    * is_nonce_long.clone()
                    * (acc_mult_after_nonce.clone()
                        - acc_mult_prev.clone() * mult_diff_nonce.clone()),
            ));


            /*
            When nonce is short (occupying only one byte), we know in advance that `mult_diff_nonce = r^5`
            as there are `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`, and `s_main.bytes[0]` bytes
            to be taken into account.
            */
            constraints.push((
                "Leaf nonce acc mult (nonce short)",
                q_enable.clone()
                    * (one.clone() - is_nonce_long.clone())
                    * (acc_mult_after_nonce.clone() - acc_mult_prev.clone() * r_table[4].clone()), // r_table[4] because of s_rlp1, s_rlp2, c_rlp1, c_rlp2, and 1 for nonce_len = 1
            ));

            /*
            We need to prepare the multiplier that will be needed in the next row: `acc_mult_final`.
            We have the multiplier after nonce bytes were added to the RLC: `acc_mult_after_nonce`.
            Now, `acc_mult_final` depends on the number of balance bytes. 
            `rlc_after_balance = rlc_after_nonce + b1 * acc_mult_after_nonce + ...
                + bl * acc_mult_after_nonce * r^{l-1}`
            Where `b1,...,bl` are `l` balance bytes. As with nonce, we do not know the length of balance bytes
            in advance. For this reason, we store `r^l` in `mult_diff_balance` and check whether:
            `acc_mult_final = acc_mult_after_nonce * mult_diff_balance`.
            Note that `mult_diff_balance` is not the last multiplier in this row, but the first in
            the next row (this is why there is `r^l` instead of `r^{l-1}`).
            */
            constraints.push((
                "Leaf balance acc mult (balance long)",
                q_enable.clone()
                    * is_balance_long.clone()
                    * (acc_mult_final.clone()
                        - acc_mult_after_nonce.clone() * mult_diff_balance.clone()),
            ));

            /*
            When balance is short, there is only one balance byte and we know in advance that the
            multiplier changes only by factor `r`.
            */
            constraints.push((
                "Leaf balance acc mult (balance short)",
                q_enable.clone()
                    * (one.clone() - is_balance_long.clone())
                    * (acc_mult_final.clone()
                        - acc_mult_after_nonce.clone() * r_table[0].clone()),
            ));

            // RLP:
            let c66 = Expression::Constant(F::from(66)); // the number of bytes in storage codehash row
            let c184 = Expression::Constant(F::from(184));
            let nonce_long_len = s_advices0_cur - c128.clone() + one.clone();

            let nonce_len =
                nonce_long_len * is_nonce_long.clone() + (one.clone() - is_nonce_long.clone());

            let balance_long_len = c_advices0_cur - c128.clone() + one.clone();
            let balance_len = balance_long_len * is_balance_long.clone()
                + (one.clone() - is_balance_long.clone());

            /*
            s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes  c_main.bytes
            184     80      248     78      nonce         balance

            Or:
            s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes                         c_main.bytes
            248     109     157     (this is key row, 157 means key of length 29)
            184     77      248     75      7 (short nonce , only one byte)      135 (means balance is of length 7) 28 ... 59
            */

            /*
            `s_main.rlp1` needs always be 184. This is RLP byte meaning that behind this byte
            there is a string of length more than 55 bytes and that only `1 = 184 - 183` byte is reserved
            for length (`s_main.rlp2`). The string is always of length greater than 55 because there
            are codehash (32 bytes) and storage root (32 bytes) in the next row as part of this string.

            The only exception is when `is_non_existing_account_proof = 1` & `is_wrong_leaf = 0`.
            In this case the value does not matter as the account leaf is only a placeholder and
            does not use `s_main.rlp1` and `s_main.rlp2`. Note that it uses `s_main` for nibbles
            because the account address is computed using nibbles and this account address needs
            to be as required by a lookup.
            */
            constraints.push(("Leaf nonce balance s_main.rlp1 = 184.", q_enable.clone()
                * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                * (s_rlp1.clone() - c184)));

            /*
            `c_main.rlp1` needs to always be 248. This is RLP byte meaning that behind this byte
            there is a list which has one byte that specifies the length - `at c_main.rlp2`.

            The only exception is when `is_non_existing_account_proof = 1` & `is_wrong_leaf = 0`.
            In this case the value does not matter as the account leaf is only a placeholder and
            does not use `c_main`. Note that it uses `s_main` for nibbles because the account address
            is computed using nibbles and this account address needs to be as required by a lookup.
            That means there is an account leaf which is just a placeholder but it still has the
            correct address.

            Example:
            [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
            248 at c_main.rlp1 means one byte for length. This byte is 76, meaning there are 76 bytes after it.
            */
            constraints.push((
                "Leaf nonce balance c_main.rlp1 = 248",
                q_enable.clone()
                // Note that the selector below is always different from 0, except when
                // `is_non_existing_account_proof = 1` & `is_wrong_leaf = 0`.
                // This is because `is_wrong_leaf` can be 1 only when `is_non_existing_account_proof = 1`
                // (see the constraint above).
                * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                * (c_rlp1.clone() - c248.clone()),
            ));

            /*
            `c_main.rlp2` specifies the length of the remaining RLP string. Note that the string
            is `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`, nonce bytes, balance bytes.
            Thus, `c_main.rlp2 = #(nonce bytes) + #(balance bytes) + 32 + 32`.
            `s_main.rlp2` - `c_main.rlp2` = 2 because of two bytes difference: `c_main.rlp1` and c_main.rlp2`.

            Example:
            [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
            We can see: `78 - 76 - 1 - 1 = 0`.
            */
            constraints.push((
                "Leaf nonce balance s_main.rlp2 - c_main.rlp2",
                q_enable.clone()
                * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                * (s_rlp2.clone() - c_rlp2.clone() - one.clone() - one.clone()),
            ));

            /*
            `c_main.rlp2 = #(nonce bytes) + #(balance bytes) + 32 + 32`.
            Note that `32 + 32` means the number of codehash bytes + the number of storage root bytes.
            */
            constraints.push((
                "Lean nonce balance c_main.rlp2",
                q_enable.clone()
                * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                * (c_rlp2.clone() - nonce_len - balance_len - c66),
            ));

            /*
            The whole RLP length of the account leaf is specified in the account leaf key row with
            `s_main.rlp1 = 248` and `s_main.rlp2`. `s_main.rlp2` in key row actually specifies the length.
            `s_main.rlp2` in nonce balance row specifies the length of the remaining string in nonce balance
            row, so we need to check that `s_main.rlp2` corresponds to the key length (in key row) and
            `s_main.rlp2` in nonce balance row. However, we need to take into account also the bytes
            where the lengths are stored:
            `s_main.rlp2 (key row) - key_len - 1 (because key_len is stored in 1 byte)
                - s_main.rlp2 (nonce balance row) - 1 (because of s_main.rlp1)
                - 1 (because of s_main.rlp2) = 0`

            Example:
            [248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
            [184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
            We can see: `106 - 33 - 1 - 70 - 1 - 1 = 0`.
            */
            constraints.push((
                "Account leaf RLP length",
                q_enable.clone()
                    * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                    * (rlp_len - key_len - one.clone() - s_rlp2 - one.clone() - one.clone()),
            ));

            constraints
        });

        let q_enable_nonce_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let mut is_nonce_long = meta.query_advice(
                sel1,
                Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            if !is_s {
                is_nonce_long = meta.query_advice(
                    sel1,
                    Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                );
            }

            q_enable * is_nonce_long
        };

        /*
        `mult_diff_nonce` needs to correspond to nonce length + 5 bytes:
        `s_main.rlp1,` `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp1`, 1 for byte with nonce length (`s_main.bytes[0]`).
        That means `mult_diff_nonce` needs to be `r^{nonce_len+5}` where `nonce_len = s_main.bytes[0] - 128`.

        Note that when nonce is short, `mult_diff_nonce` is not used (see the constraint above).
        */
        mult_diff_lookup(
            meta,
            q_enable_nonce_long, /* mult_diff_nonce is acc_r when is_nonce_short (mult_diff doesn't
                                  * need to be checked as it's not used) */
            5, /* 4 for s_rlp1, s_rlp2, c_rlp1, c_rlp1; 1 for byte with length
                * info */
            s_main.bytes[0],
            mult_diff_nonce,
            128,
            fixed_table,
        );

        // There are zeros in s_main.bytes after nonce length:
        /*
        /*
        Nonce RLC is computed over `s_main.bytes[1]`, ..., `s_main.bytes[31]` because we do not know
        the nonce length in advance. To prevent changing the nonce and setting `s_main.bytes[i]` for
        `i > nonce_len + 1` to get the correct nonce RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > nonce_len + 1`.
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
        */

        let q_enable_balance_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let mut is_balance_long = meta.query_advice(
                sel1,
                Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            if !is_s {
                is_balance_long = meta.query_advice(
                    sel1,
                    Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                );
            }

            q_enable * is_balance_long
        };

        /*
        `mult_diff_balance` needs to correspond to balance length + 1 byte for byte that contains balance length.
        That means `mult_diff_balance` needs to be `r^{balance_len+1}` where `balance_len = c_main.bytes[0] - 128`.

        Note that when balance is short, `mult_diff_balance` is not used (see the constraint above).
        */
        mult_diff_lookup(
            meta,
            q_enable_balance_long,
            1, // 1 for byte with length info
            c_main.bytes[0],
            mult_diff_balance,
            128,
            fixed_table,
        );

        /*
        /*
        Balance RLC is computed over `c_main.bytes[1]`, ..., `c_main.bytes[31]` because we do not know
        the balance length in advance. To prevent changing the balance and setting `c_main.bytes[i]` for
        `i > balance_len + 1` to get the correct balance RLC, we need to ensure that
        `c_main.bytes[i] = 0` for `i > balance_len + 1`.
        */
        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                q_enable,
                ind,
                c_main.bytes[0],
                c_main.bytes[ind],
                128,
                fixed_table,
            )
        }
        */

        /*
        Range lookups ensure that `s_main` and `c_main` columns are all bytes (between 0 - 255).
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
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // c_rlp1 is always 248 (checked above)
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp1, s_main.rlp2, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountLeafNonceBalanceConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafNonceBalanceChip<F> {
    type Config = AccountLeafNonceBalanceConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
