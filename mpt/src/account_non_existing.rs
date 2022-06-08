use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::FixedTableTag,
    param::{
        HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, LAYOUT_OFFSET,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct AccountNonExistingConfig {}

// Checks that the address does not exist.
pub(crate) struct AccountNonExistingChip<F> {
    config: AccountNonExistingConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountNonExistingChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        not_first_level: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        address_rlc: Column<Advice>,
    ) -> AccountNonExistingConfig {
        let config = AccountNonExistingConfig {};
        let one = Expression::Constant(F::one());
        // key rlc is in the first branch node
        let rot_into_first_branch_child = -20;

        // TODO: part of it is similar as in account_leaf_key, reuse some function.
        // Checks that account_non_existing_row contains the nibbles that correspond to address_rlc.
        meta.create_gate(
            "Account leaf address RLC (leaf not in first level, branch not placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let is_branch_placeholder =
                    s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET];
                let is_branch_placeholder = meta.query_advice(
                    is_branch_placeholder,
                    Rotation(rot_into_first_branch_child - 1),
                );

                let is_leaf_in_first_level =
                    one.clone() - meta.query_advice(not_first_level, Rotation::cur());

                let key_rlc_acc_start =
                    meta.query_advice(key_rlc, Rotation(rot_into_first_branch_child));
                let key_mult_start =
                    meta.query_advice(key_rlc_mult, Rotation(rot_into_first_branch_child));

                // sel1, sel2 is in init branch
                let sel1 = meta.query_advice(
                    s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let sel2 = meta.query_advice(
                    s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                    Rotation(rot_into_first_branch_child - 1),
                );

                let c32 = Expression::Constant(F::from(32));
                let c48 = Expression::Constant(F::from(48));

                // If sel1 = 1, we have nibble+48 in s_advices[0].
                let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
                let mut key_rlc_acc = key_rlc_acc_start.clone()
                    + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();
                let mut key_mult = key_mult_start.clone() * r_table[0].clone() * sel1;
                key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                // If sel2 = 1, we have 32 in s_advices[0].
                constraints.push((
                    "Account leaf key acc s_advice1",
                    q_enable.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (s_advice1 - c32)
                        * sel2,
                ));

                let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_advices[ind], Rotation::cur());
                    key_rlc_acc = key_rlc_acc + s * key_mult.clone() * r_table[ind - 3].clone();
                }

                let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
                key_rlc_acc = key_rlc_acc + c_rlp1 * key_mult.clone() * r_table[30].clone();
                key_rlc_acc = key_rlc_acc + c_rlp2 * key_mult * r_table[31].clone();

                let address_rlc = meta.query_advice(address_rlc, Rotation::cur());

                constraints.push((
                    "Account address RLC",
                    q_enable.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (key_rlc_acc.clone() - address_rlc.clone()),
                ));

                constraints
            },
        );

        range_lookups(
            meta,
            q_enable,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_rlp2, c_rlp1, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountNonExistingConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountNonExistingChip<F> {
    type Config = AccountNonExistingConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
