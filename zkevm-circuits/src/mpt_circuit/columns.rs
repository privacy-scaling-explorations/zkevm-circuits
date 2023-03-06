use eth_types::Field;
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use std::{convert::TryInto, marker::PhantomData};

use crate::mpt_circuit::param::HASH_WIDTH;

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainCols<F> {
    pub(crate) bytes: [Column<Advice>; HASH_WIDTH + 2],
    _marker: PhantomData<F>,
}

impl<F: Field> MainCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            bytes: (0..HASH_WIDTH + 2)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn expr(&self, meta: &mut VirtualCells<F>, rot: i32) -> Vec<Expression<F>> {
        self.bytes
            .iter()
            .map(|&byte| meta.query_advice(byte, Rotation(rot)))
            .collect::<Vec<_>>()
    }
}
