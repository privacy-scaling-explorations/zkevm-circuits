use gadgets::util::{not, Expr};
use halo2_proofs::{arithmetic::FieldExt, circuit::Region, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::{helpers::accumulate_rand, FixedTableTag},
    mpt_circuit::{
        helpers::{BaseConstraintBuilder, BranchNodeInfo},
        param::{
            ACCOUNT_DRIFTED_LEAF_IND, ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND,
            ACCOUNT_LEAF_NONCE_BALANCE_C_IND, ACCOUNT_LEAF_NONCE_BALANCE_S_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND,
            BRANCH_ROWS_NUM,
        },
    },
    mpt_circuit::{MPTConfig, MPTContext, ProofValues},
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

An example of leaf rows:
[248 102 157 55 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 6]
[248 102 157 32 133 130 180 167 143 97 28 115 102 25 94 62 148 249 8 6 55 244 16 75 187 208 208 127 251 120 61 73 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4]
[0 0 157 32 133 130 180 167 143 97 28 115 102 25 94 62 148 249 8 6 55 244 16 75 187 208 208 127 251 120 61 73 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 18]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 23 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 8]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 9]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 11]
[248 102 157 32 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 6 10]

The `ACCOUNT_LEAF_DRIFTED` row is nonempty when a leaf is added (or deleted) to the position in trie where there is already
an existing leaf. This appears when an existing leaf and a newly added leaf have the same initial key nibbles.
In this case, a new branch is created and both leaves (existing and newly added) appear in the new branch.
`ACCOUNT_LEAF_DRIFTED` row contains the key bytes of the existing leaf once it drifted down to the new branch.

Add case (S branch is placeholder):
Branch S           || Branch C
Placeholder branch || Added branch
Leaf S             || Leaf C
                    || Drifted leaf (this is Leaf S drifted into Added branch)

Leaf S needs to have the same RLC as Drifted leaf.
Note that Leaf S RLC is computed by taking the key RLC from Branch S and then adding
the bytes in Leaf key S row.
Drifted leaf RLC is computed by taking the key RLC from Added branch and then adding the bytes
in Drifted leaf row.

Delete case (C branch is placeholder):
Branch S                        || Branch C
Branch to be deleted            || Placeholder branch
Leaf S (leaf to be deleted)     || Leaf C
Leaf to be drifted one level up ||

Drifted leaf in added branch has the same key as it had it before it drifted
down to the new branch.

We obtain the key RLC from the branch / extension node above the placeholder branch.
We then add the remaining key nibbles that are stored in the drifted leaf key and the final RLC
needs to be the same as the one stored in `accumulators.key.rlc` in the account leaf key row
(not the drifted leaf). This means the storage leaf has the same key RLC before and after
it drifts into a new branch.

Note: Branch key RLC is in the first branch child row (not in branch init). We need to go
in the branch above the placeholder branch.

We need the intermediate key RLC right before `drifted_pos` is added to it. If the branch parallel to the placeholder branch
is an extension node, we have the intermediate RLC stored in the extension node `accumulators.key.rlc`.
If it is a regular branch, we need to go one branch above to retrieve the RLC (if there is no level above, we take 0).
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafKeyInAddedBranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyInAddedBranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let not_first_level = ctx.position_cols.not_first_level;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        // accs.acc_c contains mult_diff_nonce, initially key_rlc was
        // used for mult_diff_nonce, but it caused PoisonedConstraint
        // in extension_node_key
        let accs = ctx.accumulators;
        let drifted_pos = ctx.branch.drifted_pos;
        let denoter = ctx.denoter;
        let r = ctx.r;

        let rot_ext = -ACCOUNT_DRIFTED_LEAF_IND - 1;
        let rot_branch_init = -ACCOUNT_DRIFTED_LEAF_IND - BRANCH_ROWS_NUM;
        let rot_first_child = rot_branch_init + 1;
        let rot_first_child_prev = rot_first_child - BRANCH_ROWS_NUM;
        let rot_key_s = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND);
        let rot_key_c = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND);

        circuit!([meta, cb], {
            let mut branch = BranchNodeInfo::new(meta, s_main, true, rot_branch_init);

            // drifted leaf appears only when there is a placeholder branch
            ifx! {branch.is_s_or_c_placeholder() => {
                // `s_rlp1` is always 248 because the account leaf is always longer than 55 bytes.
                require!(a!(s_main.rlp1) => 248);

                // If is_c16 = 0, we have 32 in `s_main.bytes[1]`.
                ifx!{not!(branch.is_c16()) => {
                    require!(a!(s_main.bytes[1]) => 32);
                }}

                // We check that the leaf RLC is properly computed. RLC is then taken and
                // nonce/balance & storage root / codehash values are added to the RLC (note that nonce/balance
                // & storage root / codehash are not stored for the drifted leaf because these values stay
                // the same as in the leaf before drift).
                // Finally, a lookup is used to check the hash that corresponds to this RLC is
                // in the parent branch at `drifted_pos` position.
                let rlc = rlc::expr(
                    &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[0..36].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                require!(a!(accs.acc_s.rlc) => rlc);

                // We take the leaf RLC computed in the key row, we then add nonce/balance and storage root/codehash
                // to get the final RLC of the drifted leaf. We then check whether the drifted leaf is at
                // the `drifted_pos` in the parent branch.
                for is_s in [false, true] {
                    branch.set_is_s(is_s);

                    // Nonce balance S
                    // Nonce balance C
                    // Storage codehash S
                    // Storage codehash C
                    // Drifted leaf

                    let nonce_rot = -(ACCOUNT_DRIFTED_LEAF_IND - if is_s {ACCOUNT_LEAF_NONCE_BALANCE_S_IND} else {ACCOUNT_LEAF_NONCE_BALANCE_C_IND});
                    let storage_codehash_rot = -(ACCOUNT_DRIFTED_LEAF_IND - if is_s {ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND} else {ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND});
                    let nonce_balance_rot = -(ACCOUNT_DRIFTED_LEAF_IND - if is_s {ACCOUNT_LEAF_KEY_S_IND} else {ACCOUNT_LEAF_KEY_C_IND});

                    let is_nonce_long = a!(denoter.sel1, nonce_balance_rot);
                    let is_balance_long = a!(denoter.sel2, nonce_balance_rot);

                    let nonce_stored = a!(accs.s_mod_node_rlc, nonce_rot);
                    let nonce_rlc = ifx!{is_nonce_long => {
                        rlc::expr(&[a!(s_main.bytes[0], nonce_rot), nonce_stored.expr()], &r)
                    } elsex {
                        nonce_stored
                    }};

                    let balance_stored = a!(accs.c_mod_node_rlc, nonce_rot);
                    let balance_rlc = ifx!{is_balance_long => {
                        rlc::expr(&[a!(c_main.bytes[0], nonce_rot), balance_stored.expr()], &r)
                    } elsex {
                        balance_stored
                    }};

                    let mult_diff_nonce = a!(accs.acc_c.rlc, nonce_rot);
                    let mult_diff_balance = a!(accs.key.mult, nonce_rot);

                    // Calculate rlc
                    let rlc = a!(accs.acc_s.rlc) + rlc::expr(
                        &[
                            a!(s_main.rlp1, nonce_rot),
                            a!(s_main.rlp2, nonce_rot),
                            a!(c_main.rlp1, nonce_rot),
                            a!(c_main.rlp2, nonce_rot),
                            nonce_rlc,
                            balance_rlc,
                            a!(s_main.rlp2, storage_codehash_rot),
                            a!(accs.s_mod_node_rlc, storage_codehash_rot), // storage root rlc
                            a!(c_main.rlp2, storage_codehash_rot),
                            a!(accs.c_mod_node_rlc, storage_codehash_rot), // codehash rlc
                        ].map(|v| v * a!(accs.acc_s.mult)),
                        &[
                            r[..4].to_vec(),
                            accumulate_rand(&[mult_diff_nonce.expr(), mult_diff_balance.expr(), r[0].expr(), r[31].expr(), r[0].expr()]),
                        ].concat(),
                    );

                    // Check that `mod_node_rlc` in a placeholder branch contains the hash of the drifted leaf.
                    // (that this value corresponds to the value in the non-placeholder branch at `drifted_pos`
                    // is checked in `branch.rs`)
                    ifx!{branch.is_placeholder() => {
                        let account_len = a!(s_main.rlp2) + 2.expr();
                        require!((1, rlc, account_len, a!(accs.mod_node_rlc(is_s), rot_first_child)) => @"keccak");
                    }}
                }

                // The key RLC of the drifted leaf needs to be the same as the key RLC of the leaf before
                // the drift - the nibbles are the same in both cases, the difference is that before the
                // drift some nibbles are stored in the leaf key, while after the drift these nibbles are used as
                // position in a branch or/and nibbles of the extension node.
                let is_branch_placeholder_in_first_level = not!(a!(not_first_level, rot_branch_init));
                let key_rlc_prev = ifx!{branch.is_extension() => {
                    a!(accs.key.rlc, rot_ext)
                } elsex {
                    ifx!{not!(is_branch_placeholder_in_first_level) => {
                        a!(accs.key.rlc, rot_first_child_prev)
                    }}
                }};
                let key_mult_prev = ifx!{is_branch_placeholder_in_first_level => {
                    1.expr()
                } elsex {
                    a!(accs.key.mult, rot_first_child_prev)
                }};

                let key_mult_prev = key_mult_prev.expr() *
                ifx!{branch.is_extension() => {
                    // Get the mult_diff from the extension node.
                    a!(accs.mult_diff, rot_first_child)
                } elsex {
                    1.expr()
                }};

                // Check that the RLC matches
                let acc_key_rlc = ifx!{branch.is_s_placeholder() => {
                    a!(accs.key.rlc, rot_key_s)
                } elsex {
                    a!(accs.key.rlc, rot_key_c)
                }};
                // If is_c16 = 1, we have one nibble+48 in `s_main.bytes[1]`.
                let drifted_pos_mult = key_mult_prev.expr() * ifx!{branch.is_c16() => { 16.expr() } elsex { 1.expr() }};
                let key_rlc = key_rlc_prev + a!(drifted_pos, rot_first_child) * drifted_pos_mult + rlc::expr(
                    &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                        key_mult_prev.expr() * (if idx == 0 { (a!(byte) - 48.expr()) * branch.is_c16() } else { a!(byte) })).collect::<Vec<_>>(),
                    &r,
                );
                require!(acc_key_rlc => key_rlc);

                let num_bytes = a!(s_main.bytes[0]) - 128.expr();
                // RLC bytes zero check
                cb.set_range_length(1.expr() + num_bytes.expr());
                // Update `mult_diff` for key length + 2 RLP bytes + 1 byte that contains the
                // key length.
                require!((FixedTableTag::RMult, num_bytes + 3.expr(), a!(accs.acc_s.mult)) => @"mult");
            }}
        });

        AccountLeafKeyInAddedBranchConfig {
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        row: &[u8],
        offset: usize,
    ) {
        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len = (row[2] - 128) as usize + 3;
        mpt_config.compute_acc_and_mult(row, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

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
