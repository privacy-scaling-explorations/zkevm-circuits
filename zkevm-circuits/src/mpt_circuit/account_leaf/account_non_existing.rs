use gadgets::util::{and, not, select, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::{dot, rlc},
    mpt_circuit::columns::{AccumulatorCols, MainCols},
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{helpers::extend_rand, MPTContext},
    mpt_circuit::{
        helpers::key_len_lookup,
        param::{ACCOUNT_LEAF_KEY_C_IND, IS_NON_EXISTING_ACCOUNT_POS},
        MPTConfig,
    },
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        param::{
            ACCOUNT_NON_EXISTING_IND, BRANCH_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS,
            IS_BRANCH_C1_POS, RLP_NUM,
        },
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

The constraints in this file apply to ACCOUNT_NON_EXISTING.

For example, the row might be:
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

We are proving that there is no account at the specified address. There are two versions of proof:
    1. A leaf is returned by getProof that is not at the required address (we call this a wrong leaf).
    In this case, the `ACCOUNT_NON_EXISTING` row contains the nibbles of the address (the nibbles that remain
    after the nibbles used for traversing through the branches are removed) that was enquired
    while `ACCOUNT_LEAF_KEY` row contains the nibbles of the wrong leaf. We need to prove that
    the difference is nonzero. This way we prove that there exists some account which has some
    number of the starting nibbles the same as the enquired address (the path through branches
    above the leaf), but at the same time the full address is not the same - the nibbles stored in a leaf differ.
    2. A branch is the last element of the getProof response and there is a nil object
    at the address position. Placeholder account leaf is added in this case.
    In this case, the `ACCOUNT_NON_EXISTING` row contains the same nibbles as `ACCOUNT_LEAF_KEY` and it is
    not needed. We just need to prove that the branch contains nil object (128) at the enquired address.

The whole account leaf looks like:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

We can observe that the example account leaf above is not for non-existing account proof as the first and third
rows contain the same nibbles (the difference is solely in RLP specific bytes which are not needed
in `ACCOUNT_NON_EXISTING` row).

For the example of non-existing account proof account leaf see below:

[248 102 157 55 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 6]
[248 102 157 55 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4]
[1 0 157 56 133 130 180 167 143 97 28 115 102 25 94 62 148 249 8 6 55 244 16 75 187 208 208 127 251 120 61 73 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 18]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 8]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 9]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 11]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10]

In this case, the nibbles in the third row are different from the nibbles in the first or second row. Here, we are
proving that the account does not exist at the address which starts with the same nibbles as the leaf that is
in the rows above (except for the `ACCOUNT_NON_EXISTING` row) and continues with nibbles `ACCOUNT_NON_EXISTING` row.

Note that the selector (being 1 in this case) at `s_main.rlp1` specifies whether it is wrong leaf or nil case.

Lookups:
The `non_existing_account_proof` lookup is enabled in `ACCOUNT_NON_EXISTING` row.
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct AccountNonExistingConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountNonExistingConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let not_first_level = ctx.position_cols.not_first_level;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        // should be the same as sel2 as both parallel proofs are the same for
        // non_existing_account_proof
        let sel1 = ctx.denoter.sel1;
        let r = ctx.r;
        let address_rlc = ctx.address_rlc;

        // key rlc is in the first branch node
        let rot_into_first_branch_child = -(ACCOUNT_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);

        let add_wrong_leaf_constraints =
            |meta: &mut VirtualCells<F>, cb: &mut BaseConstraintBuilder<F>| {
                constraints! {[meta, cb], {
                    let sum = a!(accs.key.rlc);
                    let sum_prev = a!(accs.key.mult);
                    let diff_inv = a!(accs.acc_s.rlc);

                    let sum_prev_check = dot::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().map(|&byte| a!(byte, -1)).collect::<Vec<_>>(),
                        &extend_rand(&r),
                    );

                    // We compute the RLC of the key bytes in the ACCOUNT_NON_EXISTING row. We check whether the computed
                    // value is the same as the one stored in `accs.key.mult` column.
                    let sum_check = dot::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                        &extend_rand(&r),
                    );
                    require!(sum => sum_check);

                    // We compute the RLC of the key bytes in the ACCOUNT_LEAF_KEY row. We check whether the computed
                    // value is the same as the one stored in `accs.key.rlc` column.
                    require!(sum_prev => sum_prev_check);

                    // TODO(Brecht): what?
                    // The address in the ACCOUNT_LEAF_KEY row and the address in the ACCOUNT_NON_EXISTING row
                    // are different.
                    require!((sum - sum_prev) * diff_inv => 1);
                }}
            };

        // Checks that account_non_existing_row contains the nibbles that give
        // address_rlc (after considering modified_node in branches/extension
        // nodes above). Note: currently, for non_existing_account proof S and C
        // proofs are the same, thus there is never a placeholder branch.
        constraints! {[meta, cb], {
            let is_leaf_not_in_first_level = a!(not_first_level);

            // Wrong leaf has a meaning only for non existing account proof. For this proof, there are two cases:
            // 1. A leaf is returned that is not at the required address (wrong leaf).
            // 2. A branch is returned as the last element of getProof and there is nil object at address position. Placeholder account leaf is added in this case.
            let is_wrong_leaf = a!(s_main.rlp1);
            // is_wrong_leaf is checked to be bool in `account_leaf_nonce_balance.rs` (q_enable in this chip
            // is true only when non_existing_account_proof).

            /* Non existing account proof leaf address RLC (leaf not in first level, branch not placeholder) */
            ifx!{is_leaf_not_in_first_level.expr() => {
                let key_rlc_acc_start = a!(accs.key.rlc, rot_into_first_branch_child);
                let key_mult_start = a!(accs.key.mult, rot_into_first_branch_child);

                // Differently as for the other proofs, the account-non-existing proof compares `address_rlc`
                // with the address stored in `ACCOUNT_NON_EXISTING` row, not in `ACCOUNT_LEAF_KEY` row.
                // The crucial thing is that we have a wrong leaf at the address (not exactly the same, just some starting
                // set of nibbles is the same) where we are proving there is no account.
                // If there would be an account at the specified address, it would be positioned in the branch where
                // the wrong account is positioned. Note that the position is determined by the starting set of nibbles.
                // Once we add the remaining nibbles to the starting ones, we need to obtain the enquired address.
                // There is a complementary constraint which makes sure the remaining nibbles are different for wrong leaf
                // and the non-existing account (in the case of wrong leaf, while the case with nil being in branch
                // is different).
                ifx!{is_wrong_leaf => {
                    // sel1, sel2 is in init branch
                    let is_c16 = a!(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], rot_into_first_branch_child - 1);
                    let is_c1 = a!(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], rot_into_first_branch_child - 1);

                    // If c16 = 1, we have nibble+48 in s_main.bytes[0].
                    // If there is an even number of nibbles stored in a leaf, `s_bytes1` needs to be 32.
                    ifx!{is_c1 => {
                        require!(a!(s_main.bytes[1]) => 32);
                    }}

                    // set to key_mult_start * r if is_c16, else key_mult_start
                    let key_mult = key_mult_start.expr() * selectx!{is_c16 => { r[0].expr() } elsex { 1 }};
                    // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
                    let key_rlc_acc = key_rlc_acc_start + rlc::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                            (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                        &[[1.expr()].to_vec(), r.to_vec()].concat(),
                    );
                    require!(key_rlc_acc => a!(address_rlc));

                    // General wrong leaf constraints
                    add_wrong_leaf_constraints(meta, cb);
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    // Note that the constraints in `branch.rs` ensure that `sel1` is 1 if and only if there is a nil object
                    // at `modified_node` position. We check that in case of no wrong leaf in
                    // the non-existing-account proof, `is_nil_object` is 1.
                    require!(a!(sel1, rot_into_first_branch_child) => true);
                }}
            } elsex {
                ifx!{is_wrong_leaf => {
                    /* Non existing account proof leaf address RLC (leaf in first level) */
                    // Ensuring that the account does not exist when there is only one account in the state trie.
                    // Note 1: The hash of the only account is checked to be the state root in `account_leaf_storage_codehash.rs`.
                    // Note 2: There is no nil_object case checked in this gate, because it is covered in the gate
                    // above. That is because when there is a branch (with nil object) in the first level,
                    // it automatically means the account leaf is not in the first level.

                    // Note: when leaf is in the first level, the key stored in the leaf is always
                    // of length 33 - the first byte being 32 (when after branch,
                    // the information whether there the key is odd or even
                    // is in s_main.bytes[IS_BRANCH_C16_POS - LAYOUT_OFFSET] (see sel1/sel2).
                    require!(a!(s_main.bytes[1]) => 32);

                    // RLC check
                    let rlc = rlc::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[4..36].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                        &r,
                    );
                    require!(a!(address_rlc) => rlc);

                    // General wrong leaf constraints
                    add_wrong_leaf_constraints(meta, cb);
                }}
            }}

            ifx!{is_wrong_leaf => {
                /* Address of wrong leaf and the enquired address are of the same length */
                // This constraint is to prevent the attacker to prove that some account does not exist by setting
                // some arbitrary number of nibbles in the account leaf which would lead to a desired RLC.
                require!(a!(s_main.bytes[0]) => a!(s_main.bytes[0], -1));
            }}

            // Key RLC is computed over all of `s_main.bytes[1], ..., s_main.bytes[31], c_main.rlp1, c_main.rlp2`
            // because we do not know the key length in advance.
            // To prevent changing the key and setting `s_main.bytes[i]` (or `c_main.rlp1/c_main.rlp2`) for
            // `i > key_len + 1` to get the desired key RLC, we need to ensure that
            // `s_main.bytes[i] = 0` for `i > key_len + 1`.
            // Note that the number of the key bytes in the `ACCOUNT_NON_EXISTING` row needs to be the same as
            // the number of the key bytes in the `ACCOUNT_LEAF_KEY` row.
            // Note: the key length is always in s_main.bytes[0] here as opposed to storage
            // key leaf where it can appear in `s_rlp2` too. This is because the account
            // leaf contains nonce, balance, ... which makes it always longer than 55 bytes,
            // which makes a RLP to start with 248 (`s_rlp1`) and having one byte (in `s_rlp2`)
            // for the length of the remaining stream.
            /*if check_zeros {
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
            }*/
        }}

        AccountNonExistingConfig {
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        offset: usize,
    ) {
        let leaf_key_c =
            &witness[offset - (ACCOUNT_NON_EXISTING_IND - ACCOUNT_LEAF_KEY_C_IND) as usize];
        let row = &witness[offset];
        let key_len = leaf_key_c.get_byte(2) as usize - 128;
        let mut sum = F::zero();
        let mut sum_prev = F::zero();
        let mut mult = mpt_config.randomness;
        for i in 0..key_len {
            sum += F::from(row.get_byte(3 + i) as u64) * mult;
            sum_prev += F::from(leaf_key_c.get_byte(3 + i) as u64) * mult;
            mult *= mpt_config.randomness;
        }
        let mut diff_inv = F::zero();
        if sum != sum_prev {
            diff_inv = F::invert(&(sum - sum_prev)).unwrap();
        }

        region
            .assign_advice(
                || "assign sum".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(sum),
            )
            .ok();
        region
            .assign_advice(
                || "assign sum prev".to_string(),
                mpt_config.accumulators.key.mult,
                offset,
                || Value::known(sum_prev),
            )
            .ok();
        region
            .assign_advice(
                || "assign diff inv".to_string(),
                mpt_config.accumulators.acc_s.rlc,
                offset,
                || Value::known(diff_inv),
            )
            .ok();

        if row.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) == 1 {
            region
                .assign_advice(
                    || "assign lookup enabled".to_string(),
                    mpt_config.proof_type.proof_type,
                    offset,
                    || Value::known(F::from(4_u64)), /* non existing account lookup enabled in
                                                      * this row if it is non_existing_account
                                                      * proof */
                )
                .ok();
        }
    }
}
