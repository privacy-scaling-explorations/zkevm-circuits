use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::HASH_WIDTH;

#[derive(Clone, Debug)]
pub(crate) struct AddressComprConfig {}

// AddressComprChip verifies the compression of account leaf key from nibbles to hex.
// This chip is similar to KeyComprChip, the difference is that the RLP is here always longer
// than 55 bytes which means key length is always at s_advices[0] and thus we don't need to handle
// two cases (key length at s_rlp2 or s_advices[0]) separately.

// TODO: it checks (to be enabled) also the path in trie corresponds to the address (rename chip too)
pub(crate) struct AddressComprChip<F> {
    config: AddressComprConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AddressComprChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        key_rlc_r: F,
    ) -> AddressComprConfig {
        let config = AddressComprConfig {};

        meta.create_gate("Account leaf key", |meta| {
            let q_enable = q_enable(meta);

            let mut constraints = vec![];

            // TODO: when value is long so long that RLP is longer than 55 bytes

            let is_odd = meta.query_advice(s_rlp1, Rotation::cur());
            let is_even = meta.query_advice(s_rlp2, Rotation::cur());

            // TODO: is_odd, is_even are booleans
            // TODO: is_odd + is_even = 1

            // TODO: check RLP meta data

            let rotation = -3;
            let one = Expression::Constant(F::one());
            let c128 = Expression::Constant(F::from_u64(128));
            let s_advices0 =
                meta.query_advice(s_advices[0], Rotation(rotation));

            let key_len = s_advices0 - c128;
            let mut counter = Expression::Constant(F::zero());
            let mut is_key = Expression::Constant(F::one());
            // counter increases when we move through key bytes
            // when counter reaches key_len, is_key becomes 0
            // (that means we don't check equivalence between bytes and nibbles anymore)

            is_key = is_key * (key_len.clone() - counter.clone());

            let c48 = Expression::Constant(F::from_u64(48));
            let s_advices1_prev =
                meta.query_advice(s_advices[1], Rotation(rotation));
            let s_advices1_cur =
                meta.query_advice(s_advices[0], Rotation::cur());
            constraints.push((
                "Key compression odd 1",
                q_enable.clone()
                    * is_odd.clone()
                    * is_key.clone()
                    * (s_advices1_prev - s_advices1_cur - c48),
            ));

            let c16 = Expression::Constant(F::from_u64(16));
            // s_advices[i+1]_prev = s_advices[2*i - 1]_cur * 16 + s_advices[2*i]_cur
            // we can go up to i = 15
            for ind in 1..16 {
                let s_prev =
                    meta.query_advice(s_advices[ind + 1], Rotation(rotation));
                let s_cur1 =
                    meta.query_advice(s_advices[2 * ind - 1], Rotation::cur());
                let s_cur2 =
                    meta.query_advice(s_advices[2 * ind], Rotation::cur());
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

                counter = counter + one.clone();
                is_key = is_key * (key_len.clone() - counter.clone());

                constraints.push((
                    "Key compression odd 2",
                    q_enable.clone() * is_odd.clone() * is_key.clone() * expr,
                ));
            }

            // s_advices[17]_prev = s_advices[31]_cur * 16 + c_rlp1_cur
            let s_prev = meta.query_advice(s_advices[17], Rotation(rotation));
            let s_cur1 =
                meta.query_advice(s_advices[HASH_WIDTH - 1], Rotation::cur());
            let s_cur2 = meta.query_advice(c_rlp1, Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

            counter = counter + one.clone();
            is_key = is_key * (key_len.clone() - counter.clone());

            constraints.push((
                "Key compression odd 3",
                q_enable.clone() * is_odd.clone() * is_key.clone() * expr,
            ));

            // s_advices[18]_prev = c_rlp2 * 16 + c_advices[0]
            let s_prev = meta.query_advice(s_advices[18], Rotation(rotation));
            let s_cur1 = meta.query_advice(c_rlp2, Rotation::cur());
            let s_cur2 = meta.query_advice(c_advices[0], Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

            counter = counter + one.clone();
            is_key = is_key * (key_len.clone() - counter.clone());

            constraints.push((
                "Key compression odd 4",
                q_enable.clone() * is_odd.clone() * is_key.clone() * expr,
            ));
            // we can check from i = 19
            for ind in 19..HASH_WIDTH {
                let s_prev =
                    meta.query_advice(s_advices[ind], Rotation(rotation));
                let s_cur1 = meta.query_advice(
                    c_advices[2 * (ind - 18) - 1],
                    Rotation::cur(),
                );
                let s_cur2 = meta
                    .query_advice(c_advices[2 * (ind - 18)], Rotation::cur());
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

                counter = counter + one.clone();
                is_key = is_key * (key_len.clone() - counter.clone());

                constraints.push((
                    "Key compression odd 5",
                    q_enable.clone() * is_odd.clone() * is_key.clone() * expr,
                ));
            }

            let s_prev = meta.query_advice(c_rlp1, Rotation(rotation));
            let s_cur1 = meta
                .query_advice(c_advices[2 * (32 - 18) - 1], Rotation::cur());
            let s_cur2 =
                meta.query_advice(c_advices[2 * (32 - 18)], Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

            counter = counter + one.clone();
            is_key = is_key * (key_len.clone() - counter.clone());

            constraints.push((
                "Key compression odd 6",
                q_enable.clone() * is_odd.clone() * is_key.clone() * expr,
            ));

            // if key length is even, the first (of the rest) byte contains 32

            let mut counter = Expression::Constant(F::zero());
            let mut is_key = Expression::Constant(F::one());
            // counter increases when we move through key bytes
            // when counter reaches key_len, is_key becomes 0
            // (that means we don't check equivalence between bytes and nibbles anymore)

            is_key = is_key * (key_len.clone() - counter.clone());

            let c32 = Expression::Constant(F::from_u64(32));
            let s_advices0_prev =
                meta.query_advice(s_advices[1], Rotation(rotation));
            constraints.push((
                "Key compression even 1",
                q_enable.clone()
                    * is_even.clone()
                    * is_key.clone()
                    * (s_advices0_prev - c32),
            ));
            // s_advices[i+1]_prev = s_advices[2*i - 1]_cur * 16 + s_advices[2*i]_cur
            // we can go up to i = 16
            for ind in 1..17 {
                let s_prev =
                    meta.query_advice(s_advices[ind + 1], Rotation(rotation));
                let s_cur1 =
                    meta.query_advice(s_advices[2 * ind - 2], Rotation::cur());
                let s_cur2 =
                    meta.query_advice(s_advices[2 * ind - 1], Rotation::cur());
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

                counter = counter + one.clone();
                is_key = is_key * (key_len.clone() - counter.clone());

                constraints.push((
                    "Key compression even 2",
                    q_enable.clone() * is_even.clone() * is_key.clone() * expr,
                ));
            }

            // s_advices[18]_prev = c_rlp1_cur * 16 + c_rlp2_cur
            let s_prev = meta.query_advice(s_advices[18], Rotation(rotation));
            let c_rlp1_cur = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2_cur = meta.query_advice(c_rlp2, Rotation::cur());
            let expr =
                s_prev - c_rlp1_cur.clone() * c16.clone() - c_rlp2_cur.clone();

            counter = counter + one.clone();
            is_key = is_key * (key_len.clone() - counter.clone());

            constraints.push((
                "Key compression even 3",
                q_enable.clone() * is_even.clone() * is_key.clone() * expr,
            ));
            // we can check from i = 19
            for ind in 19..HASH_WIDTH {
                let s_prev =
                    meta.query_advice(s_advices[ind], Rotation(rotation));
                let s_cur1 = meta.query_advice(
                    c_advices[2 * (ind - 18) - 2],
                    Rotation::cur(),
                );
                let s_cur2 = meta.query_advice(
                    c_advices[2 * (ind - 18) - 1],
                    Rotation::cur(),
                );
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

                counter = counter + one.clone();
                is_key = is_key * (key_len.clone() - counter.clone());

                constraints.push((
                    "Key compression even 4",
                    q_enable.clone() * is_even.clone() * is_key.clone() * expr,
                ));
            }

            let s_prev = meta.query_advice(c_rlp1, Rotation(rotation));
            let s_cur1 = meta
                .query_advice(c_advices[2 * (32 - 18) - 2], Rotation::cur());
            let s_cur2 = meta
                .query_advice(c_advices[2 * (32 - 18) - 1], Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;

            counter = counter + one.clone();
            is_key = is_key * (key_len.clone() - counter.clone());

            constraints.push((
                "Key compression even 5",
                q_enable.clone() * is_even.clone() * is_key.clone() * expr,
            ));

            // We need to make sure there are 0s after nibbles end
            // We have 2 * key_len nibbles, this is at most 64. We need to check
            // s_advices, c_rlp1, c_rlp2, c_advices to be 0 after 2 * key_len nibbles.
            // s_advices, c_rlp1, c_rlp2, c_advices are 32 + 2 + 32 = 66.

            let nibble_len =
                is_even * (key_len.clone() - one.clone()) * F::from_u64(2)
                    + is_odd
                        * ((key_len.clone() - one.clone()) * F::from_u64(2)
                            + one.clone());
            let c66 = Expression::Constant(F::from_u64(66));
            let mut counter = Expression::Constant(F::zero());
            let mut is_not_nibble = Expression::Constant(F::one());
            // is_not_nibble becomes 0 in the positions where we have nibbles

            for ind in (0..HASH_WIDTH).rev() {
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push((
                    "Not nibble c_advices",
                    q_enable.clone() * is_not_nibble.clone() * c,
                ));

                counter = counter + one.clone();
                is_not_nibble = is_not_nibble
                    * (c66.clone() - nibble_len.clone() - counter.clone());
            }

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            constraints.push((
                "Not nibble c_rlp1",
                q_enable.clone() * is_not_nibble.clone() * c_rlp1,
            ));

            counter = counter + one.clone();
            is_not_nibble = is_not_nibble
                * (c66.clone() - nibble_len.clone() - counter.clone());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            constraints.push((
                "Not nibble c_rlp2",
                q_enable.clone() * is_not_nibble.clone() * c_rlp2,
            ));

            for ind in (0..HASH_WIDTH).rev() {
                counter = counter + one.clone();
                is_not_nibble = is_not_nibble
                    * (c66.clone() - nibble_len.clone() - counter.clone());

                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                constraints.push((
                    "Not nibble s_advices",
                    q_enable.clone() * is_not_nibble.clone() * s,
                ));
            }

            // rlc is in the first branch node
            // -24 = -3 (leaf c) - 3 (leaf s) - 16 (branch nodes)
            let mut key_rlc_acc = meta.query_advice(key_rlc, Rotation(-24));
            let mut key_mult = meta.query_advice(key_rlc_mult, Rotation(-24));

            for ind in 0..HASH_WIDTH {
                let n = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc = key_rlc_acc + n * key_mult.clone();
                key_mult = key_mult * key_rlc_r;
            }
            key_rlc_acc = key_rlc_acc + c_rlp1_cur * key_mult.clone(); // c_rlp1
            key_mult = key_mult * key_rlc_r;
            key_rlc_acc = key_rlc_acc + c_rlp2_cur * key_mult.clone(); // c_rlp2
            key_mult = key_mult * key_rlc_r;
            for ind in 0..HASH_WIDTH {
                let n = meta.query_advice(c_advices[ind], Rotation::cur());
                key_rlc_acc = key_rlc_acc + n * key_mult.clone();
                key_mult = key_mult * key_rlc_r;
            }

            // RLC of key nibbles are to be checked to verify that the proper key is used.
            // TODO: enable this when key in mpt.rs is available. This is to ensure
            // the node in trie has been modified that correspond to the key.
            /*
            let key_rlc = meta.query_advice(key_rlc, Rotation::cur());
            constraints
                .push(("Key RLC", q_enable.clone() * (key_rlc_acc - key_rlc)));
            */

            constraints
        });

        config
    }

    pub fn construct(config: AddressComprConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AddressComprChip<F> {
    type Config = AddressComprConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
