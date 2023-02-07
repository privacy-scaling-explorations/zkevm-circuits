use halo2_proofs::{arithmetic::FieldExt, circuit::Region, plonk::VirtualCells, poly::Rotation};

use crate::{
    circuit,
    circuit_tools::{CellManager, ConstraintBuilder},
    mpt_circuit::{
        helpers::BranchNodeInfo,
        param::{
            ACCOUNT_DRIFTED_LEAF_IND, ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND,
            ACCOUNT_LEAF_NONCE_BALANCE_C_IND, ACCOUNT_LEAF_NONCE_BALANCE_S_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND,
            BRANCH_ROWS_NUM, RLP_LIST_LONG,
        },
    },
    mpt_circuit::{
        helpers::{get_parent_rlc_state, AccountLeafInfo, KeyData, MPTConstraintBuilder},
        FixedTableTag,
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

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyInAddedBranchConfig<F> {
    key_data: KeyData<F>,
}

impl<F: FieldExt> AccountLeafKeyInAddedBranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let not_first_level = ctx.position_cols.not_first_level;
        let s_main = ctx.s_main;
        let accs = ctx.accumulators;
        let r = ctx.r.clone();

        let mut cm = CellManager::new(meta, 1, &ctx.managed_columns, 0);
        let ctx_key_data: Option<KeyData<F>>;

        let rot_parent = -ACCOUNT_DRIFTED_LEAF_IND - 1;
        let rot_branch_init = rot_parent + 1 - BRANCH_ROWS_NUM;
        let rot_first_child = rot_branch_init + 1;
        let rot_key_s = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_S_IND);
        let rot_key_c = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_KEY_C_IND);
        let rot_nonce_s = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND);
        let rot_nonce_c = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_NONCE_BALANCE_C_IND);
        let rot_storage_s = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND);
        let rot_storage_c = -(ACCOUNT_DRIFTED_LEAF_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND);

        circuit!([meta, cb.base], {
            let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
            let drifted_account = AccountLeafInfo::new(meta, ctx.clone(), 0);

            // A drifted leaf appears only when there is a placeholder branch
            ifx! {branch.is_placeholder_s_or_c() => {
                // Calculate and store the leaf RLC (RLP + key)
                let drifted_rlc = a!(accs.acc_s.rlc);
                require!(drifted_rlc => ctx.rlc(meta, 0..36, 0));

                // `s_rlp1` is always RLP_LIST_LONG + 1 because the account leaf is always > 55 bytes (and < 256)
                require!(a!(s_main.rlp1) => RLP_LIST_LONG + 1);

                // The key RLC of the drifted leaf needs to be the same as the key RLC of the leaf before
                // the drift - the nibbles are the same in both cases, the difference is that before the
                // drift some nibbles are stored in the leaf key, while after the drift these nibbles are used as
                // position in a branch or/and nibbles of the extension node.
                let is_branch_in_first_level = not!(a!(not_first_level, rot_branch_init));
                let (key_rlc_prev, key_mult_prev) = get_parent_rlc_state(meta, ctx.clone(), is_branch_in_first_level, rot_parent);

                // Load the last key values
                let key_data = KeyData::load(&mut cb.base, &mut cm, &ctx.memory["key"], 3.expr());

                // TODO(Brecht): make this work with loaded key data when extension node is separate
                ifx! {not!(branch.is_extension()) => {
                    require!(key_data.rlc => key_rlc_prev);
                    require!(key_data.mult => key_mult_prev);
                }}

                // Calculate the drifted key RLC
                let drifted_key_rlc = key_rlc_prev +
                    branch.drifted_nibble_rlc(meta, &mut cb.base, key_mult_prev.expr()) +
                    drifted_account.key_rlc(meta, &mut cb.base, key_mult_prev.expr(), branch.is_key_odd(), r[0].expr(), 0);

                // RLC bytes zero check
                let num_bytes = drifted_account.num_bytes_on_key_row(meta);
                cb.set_length(num_bytes.expr());
                // Update `mult_diff`
                let mult = a!(accs.acc_s.mult);
                require!((FixedTableTag::RMult, num_bytes.expr(), mult) => @"mult");

                // Check that the drifted leaf is unchanged and is stored at `drifted_index`.
                let calc_rlc = |is_s, meta: &mut VirtualCells<'_, F>, cb: &mut ConstraintBuilder<F>| {
                    circuit!([meta, cb], {
                        let rot_key = if is_s { rot_key_s } else { rot_key_c };
                        let rot_nonce = if is_s { rot_nonce_s } else { rot_nonce_c };
                        let rot_storage = if is_s { rot_storage_s } else { rot_storage_c };

                        let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key);

                        // Calculate the drifted leaf rlc
                        // Nonce data rlc
                        let nonce_stored = a!(accs.s_mod_node_rlc, rot_nonce);
                        let nonce_rlc = account.to_data_rlc(meta, ctx.s_main, nonce_stored, account.is_nonce_long(), rot_nonce);
                        // Balance data rlc
                        let balance_stored = a!(accs.c_mod_node_rlc, rot_nonce);
                        let balance_rlc = account.to_data_rlc(meta, ctx.c_main, balance_stored, account.is_balance_long(), rot_nonce);
                        let mult_nonce = a!(accs.acc_c.rlc, rot_nonce);
                        let mult_balance = a!(accs.key.mult, rot_nonce);
                        let rlc = drifted_rlc.expr() + account.nonce_balance_rlc(meta, nonce_rlc.expr(), balance_rlc.expr(), mult.expr(), mult_nonce.expr(), rot_nonce);
                        // Add storage/codehash rlc
                        let storage_rlc = a!(accs.s_mod_node_rlc, rot_storage);
                        let codehash_rlc = a!(accs.c_mod_node_rlc, rot_storage);
                        let mult_prev = mult.expr() * mult_nonce.expr() * mult_balance.expr();
                        let rlc = rlc + account.storage_codehash_rlc(meta, storage_rlc.expr(), codehash_rlc.expr(), mult_prev.expr(), rot_storage);

                        (true.expr(), a!(accs.key.rlc, rot_key), rlc, a!(accs.mod_node_rlc(is_s), rot_first_child))
                    })
                };
                let (do_checks, key_rlc, drifted_rlc, mod_hash) = matchx! {
                    branch.is_placeholder_s() => {
                        // Neighbour leaf in the added branch
                        // - `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                        // in a new branch.
                        // - `s_mod_node_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                        // This is because `c_mod_node_rlc` in the added branch stores the hash of
                        // `modified_index` (the leaf that has been added).
                        calc_rlc(true, meta, &mut cb.base)
                    },
                    branch.is_placeholder_c() => {
                        // Neighbour leaf in the deleted branch
                        // -`leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                        // has been deleted (and there were only two leaves, so the branch was deleted).
                        // - `c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                        // This is because `s_mod_node_rlc` in the deleted branch stores the hash of
                        // `modified_index` (the leaf that is to be deleted).
                        calc_rlc(false, meta, &mut cb.base)
                    },
                    _ => (false.expr(), 0.expr(), 0.expr(), 0.expr()),
                };
                ifx! {do_checks => {
                    // The key of the drifted leaf needs to match the key of the leaf
                    require!(key_rlc => drifted_key_rlc);
                    // The drifted leaf needs to be stored in the branch at `drifted_index`.
                    require!((1, drifted_rlc, drifted_account.num_bytes(meta), mod_hash) => @"keccak");
                }}

                ctx_key_data = Some(key_data);
            }}
        });

        AccountLeafKeyInAddedBranchConfig {
            key_data: ctx_key_data.unwrap(),
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

        self.key_data
            .witness_load(region, offset, &mut pv.memory["key"], 3)
            .ok();

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
