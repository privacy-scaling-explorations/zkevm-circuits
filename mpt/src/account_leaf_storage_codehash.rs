use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::range_lookups,
    mpt::FixedTableTag,
    param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH},
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafStorageCodehashConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct AccountLeafStorageCodehashChip<F> {
    config: AccountLeafStorageCodehashConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafStorageCodehashChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_account_leaf_storage_codehash: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc_r: F,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        mod_node_hash_rlc: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        is_s: bool,
    ) -> AccountLeafStorageCodehashConfig {
        let config = AccountLeafStorageCodehashConfig {};
        let one = Expression::Constant(F::one());

        // We don't need to check acc_mult because it's not used after this row.

        meta.create_gate("account leaf storage codehash", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut q_enable = q_not_first.clone()
                * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            let mut constraints = vec![];

            // We have storage length in s_rlp2 (which is 160 presenting 128 + 32).
            // We have storage hash in s_advices.
            // We have codehash length in c_rlp2 (which is 160 presenting 128 + 32).
            // We have codehash in c_advices.

            // Rows:
            // account leaf key
            // account leaf nonce balance S
            // account leaf nonce balance C
            // account leaf storage codeHash S
            // account leaf storage codeHash C

            let c160 = Expression::Constant(F::from(160));
            let rot = -2;
            let acc_prev = meta.query_advice(acc, Rotation(rot));
            let acc_mult_prev = meta.query_advice(acc_mult, Rotation(rot));
            let mut curr_r = acc_mult_prev;
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            constraints.push((
                "account leaf storage codehash s_rlp2",
                q_enable.clone() * (s_rlp2.clone() - c160.clone()),
            ));
            constraints.push((
                "account leaf storage codehash c_rlp2",
                q_enable.clone() * (c_rlp2.clone() - c160),
            ));

            let mut expr = acc_prev + s_rlp2 * curr_r.clone();
            curr_r = curr_r * acc_r;
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                expr = expr + s * curr_r.clone();
                curr_r = curr_r * acc_r;
            }

            expr = expr + c_rlp2 * curr_r.clone();
            curr_r = curr_r * acc_r;
            for col in c_advices.iter() {
                let c = meta.query_advice(*col, Rotation::cur());
                expr = expr + c * curr_r.clone();
                curr_r = curr_r * acc_r;
            }

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("account leaf storage codehash acc", q_enable * (expr - acc)));

            constraints
        });

        // Check hash of a leaf to be state root when leaf without branch.
        // TODO: prepare test
        meta.lookup_any(
            "account first level leaf without branch - compared to root",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let mut is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                let rlc = meta.query_advice(acc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                constraints.push((
                    q_not_first.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * (one.clone() - not_first_level.clone())
                        * rlc,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    q_not_first
                        * is_account_leaf_storage_codehash
                        * (one.clone() - not_first_level)
                        * root,
                    keccak_table_i,
                ));

                constraints
            },
        );

        // Check hash of a leaf.
        meta.lookup_any("account_leaf_storage_codehash: hash of a leaf", |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            let mut is_account_leaf_storage_codehash =
                meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            // TODO: test for account proof with only leaf (without branch)
            let mut leaf_without_branch = one.clone() - meta.query_fixed(q_not_first, Rotation(-3));
            if !is_s {
                leaf_without_branch = one.clone() - meta.query_fixed(q_not_first, Rotation(-4));
            }

            // Note: accumulated in s (not in c) for c:
            let acc_s = meta.query_advice(acc, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * (one.clone() - leaf_without_branch.clone())
                    * is_account_leaf_storage_codehash.clone()
                    * acc_s,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            // Any rotation that lands into branch can be used instead of -17.
            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation(-17));
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                not_first_level.clone()
                    * (one.clone() - leaf_without_branch.clone())
                    * is_account_leaf_storage_codehash.clone()
                    * mod_node_hash_rlc_cur,
                keccak_table_i,
            ));

            constraints
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut q_enable = q_not_first.clone()
                * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            q_enable
        };

        range_lookups(
            meta,
            sel.clone(),
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel.clone(),
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // s_rlp1 and c_rlp1 not used
        range_lookups(
            meta,
            sel,
            [s_rlp2, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountLeafStorageCodehashConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafStorageCodehashChip<F> {
    type Config = AccountLeafStorageCodehashConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
