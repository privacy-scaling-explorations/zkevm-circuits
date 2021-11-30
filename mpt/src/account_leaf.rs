use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct AccountLeafChip<F> {
    config: AccountLeafConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        branch_acc_r: F,
        sc_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> AccountLeafConfig {
        let config = AccountLeafConfig {};

        meta.create_gate("account leaf", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // [248,78,130,18,138,136,33,40,142,198,128,211,61,32,160,211,193,60,172,211,5,56,197,142,83,128,89,64,43,239,126,252,208,254,86,205,43,118,150,9,91,97,35,134,86,23,79,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,112]
            // 248, 78 is RLP meta data
            // 130 is nonce RLP meta data; 18, 138 is nonce

            let c128 = Expression::Constant(F::from_u64(128 as u64));
            let nonce_rlp_len =
                meta.query_advice(s_advices[0], Rotation::cur()) - c128;

            for ind in (1..HASH_WIDTH).rev() {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());

                constraints.push(("Foo", q_enable.clone() * s));
            }

            constraints
        });

        config
    }

    pub fn construct(config: AccountLeafConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafChip<F> {
    type Config = AccountLeafConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
