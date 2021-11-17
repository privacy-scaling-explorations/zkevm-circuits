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
pub(crate) struct KeyComprConfig {
    range_table: Column<Fixed>,
}

// KeyComprChip verifies the compression of a leaf key from nibbles to hex.
pub(crate) struct KeyComprChip<F> {
    config: KeyComprConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeyComprChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
    ) -> KeyComprConfig {
        let range_table = meta.fixed_column();

        let config = KeyComprConfig { range_table };

        meta.create_gate("Leaf key", |meta| {
            let q_enable = q_enable(meta);

            let mut constraints = vec![];

            let is_odd = meta.query_advice(s_rlp1, Rotation::cur());
            let is_even = meta.query_advice(s_rlp2, Rotation::cur());

            // TODO: is_odd, is_even are booleans
            // TODO: is_odd + is_even = 1

            // TODO: check RLP meta data

            // Leaf S
            // first two bytes (s_rlp1, s_rlp2) are RLP meta data
            // [226,160,59,138,106,70,105,186,
            // compressed key is stored in s_advices
            // value is stored in c_rlp1

            // Leaf key S
            // first two positions tell whether key length (in hex) is odd [1, 0] or even [0, 1]
            // [1,0,11,8,10,6,10,4,6,6,9,11,10,2,5,0,13,2

            // if key length is odd, the first (of the rest) byte contains 32 + 16 + first nibble
            // s_advices[0]_prev = 59 = 48 + s_advices[0]_cur = 48 + 11
            // s_advices[1]_prev = 138 = 8 * 16 + 10 = s_advices[1]_cur * 16 + s_advices[2]_cur
            // s_advices[2]_prev = 106 = 6 * 16 + 10 = s_advices[3]_cur * 16 + s_advices[4]_cur

            let c48 = Expression::Constant(F::from_u64(48));
            let s_advices0_prev =
                meta.query_advice(s_advices[0], Rotation::prev());
            let s_advices0_cur =
                meta.query_advice(s_advices[0], Rotation::cur());
            constraints.push((
                "Key compression odd 1",
                q_enable.clone()
                    * is_odd.clone()
                    * (s_advices0_prev - s_advices0_cur - c48),
            ));

            let c16 = Expression::Constant(F::from_u64(16));
            // s_advices[i]_prev = s_advices[2*i - 1]_cur * 16 + s_advices[2*i]_cur
            // we can go up to i = 15
            for ind in 1..16 {
                let s_prev =
                    meta.query_advice(s_advices[ind], Rotation::prev());
                let s_cur1 =
                    meta.query_advice(s_advices[2 * ind - 1], Rotation::cur());
                let s_cur2 =
                    meta.query_advice(s_advices[2 * ind], Rotation::cur());
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
                constraints.push((
                    "Key compression odd 2",
                    q_enable.clone() * is_odd.clone() * expr,
                ));
            }
            // s_advices[16]_prev = s_advices[31]_cur * 16 + c_rlp1_cur
            let s_prev = meta.query_advice(s_advices[16], Rotation::prev());
            let s_cur1 =
                meta.query_advice(s_advices[HASH_WIDTH - 1], Rotation::cur());
            let s_cur2 = meta.query_advice(c_rlp1, Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
            constraints.push((
                "Key compression odd 3",
                q_enable.clone() * is_odd.clone() * expr,
            ));
            // s_advices[17]_prev = c_rlp2 * 16 + c_advices[0]
            let s_prev = meta.query_advice(s_advices[17], Rotation::prev());
            let s_cur1 = meta.query_advice(c_rlp2, Rotation::cur());
            let s_cur2 = meta.query_advice(c_advices[0], Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
            constraints.push((
                "Key compression odd 4",
                q_enable.clone() * is_odd.clone() * expr,
            ));
            // we can check from i = 18
            for ind in 18..HASH_WIDTH {
                let s_prev =
                    meta.query_advice(s_advices[ind], Rotation::prev());
                let s_cur1 = meta.query_advice(
                    c_advices[2 * (ind - 17) - 1],
                    Rotation::cur(),
                );
                let s_cur2 = meta
                    .query_advice(c_advices[2 * (ind - 17)], Rotation::cur());
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
                constraints.push((
                    "Key compression odd 5",
                    q_enable.clone() * is_odd.clone() * expr,
                ));
            }

            // TODO: can be leaf S (and leaf C) of different length than 32?

            // if key length is even, the first (of the rest) byte contains 32

            let c32 = Expression::Constant(F::from_u64(32));
            let s_advices0_prev =
                meta.query_advice(s_advices[0], Rotation::prev());
            constraints.push((
                "Key compression even 1",
                q_enable.clone() * is_even.clone() * (s_advices0_prev - c32),
            ));
            // s_advices[i]_prev = s_advices[2*i - 1]_cur * 16 + s_advices[2*i]_cur
            // we can go up to i = 16
            for ind in 1..17 {
                let s_prev =
                    meta.query_advice(s_advices[ind], Rotation::prev());
                let s_cur1 =
                    meta.query_advice(s_advices[2 * ind - 2], Rotation::cur());
                let s_cur2 =
                    meta.query_advice(s_advices[2 * ind - 1], Rotation::cur());
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
                constraints.push((
                    "Key compression even 2",
                    q_enable.clone() * is_even.clone() * expr,
                ));
            }

            // s_advices[17]_prev = c_rlp1_cur * 16 + c_rlp2_cur
            let s_prev = meta.query_advice(s_advices[17], Rotation::prev());
            let s_cur1 = meta.query_advice(c_rlp1, Rotation::cur());
            let s_cur2 = meta.query_advice(c_rlp2, Rotation::cur());
            let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
            constraints.push((
                "Key compression even 3",
                q_enable.clone() * is_even.clone() * expr,
            ));
            // we can check from i = 18
            for ind in 18..HASH_WIDTH {
                let s_prev =
                    meta.query_advice(s_advices[ind], Rotation::prev());
                let s_cur1 = meta.query_advice(
                    c_advices[2 * (ind - 17) - 2],
                    Rotation::cur(),
                );
                let s_cur2 = meta.query_advice(
                    c_advices[2 * (ind - 17) - 1],
                    Rotation::cur(),
                );
                let expr = s_prev - s_cur1 * c16.clone() - s_cur2;
                constraints.push((
                    "Key compression even 4",
                    q_enable.clone() * is_even.clone() * expr,
                ));
            }

            constraints
        });

        config
    }

    pub fn construct(config: KeyComprConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for KeyComprChip<F> {
    type Config = KeyComprConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
