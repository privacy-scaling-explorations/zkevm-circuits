use crate::evm_circuit::table::RwTableTag;
use crate::util::Expr;
use eth_types::{Address, Field, ToScalar};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::convert::TryInto;
use std::marker::PhantomData;

pub trait ToBits<const N: usize> {
    fn to_bits(&self) -> [bool; N];
}

impl ToBits<4> for RwTableTag {
    fn to_bits(&self) -> [bool; 4] {
        let mut bits = [false; 4];
        let mut x = *self as u8;
        for i in 0..4 {
            bits[3 - i] = x % 2 == 1;
            x /= 2;
        }
        bits
    }
}

#[derive(Clone, Copy)]
pub struct Config<T, const N: usize>
where
    T: ToBits<N>,
{
    pub bits: [Column<Advice>; N],
    _marker: PhantomData<T>,
}

impl Config<RwTableTag, 4> {
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: RwTableTag,
    ) -> Result<(), Error> {
        for (&column, &bit) in self.bits.iter().zip(&value.to_bits()) {
            region.assign_advice(
                || format!("RwTableTag bit {:?}", column),
                column,
                offset,
                || Ok(if bit { F::one() } else { F::zero() }),
            )?;
        }
        Ok(())
    }

    pub fn value<F: Field>(
        &self,
        rotation: Rotation,
    ) -> impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F> + '_ {
        let bits = self.bits.clone();
        move |meta: &mut VirtualCells<'_, F>| {
            let bits = self.bits.map(|bit| meta.query_advice(bit, rotation));
            bits.iter()
                .fold(0.expr(), |result, bit| bit.clone() + result * 2.expr())
        }
    }
}

pub struct Chip<F: Field, T, const N: usize>
where
    T: ToBits<N>,
{
    config: Config<T, N>,
    _marker: PhantomData<F>,
}

impl<F: Field, T, const N: usize> Chip<F, T, N>
where
    T: ToBits<N>,
{
    pub fn construct(config: Config<T, N>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>, selector: Column<Fixed>) -> Config<T, N> {
        let bits = [0; N].map(|_| meta.advice_column());
        bits.map(|bit| {
            meta.create_gate("bit column is 0 or 1", |meta| {
                let selector = meta.query_fixed(selector, Rotation::cur());
                let bit = meta.query_advice(bit, Rotation::cur());
                vec![selector * bit.clone() * (1.expr() - bit)]
            })
        });

        Config {
            bits,
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: RwTableTag,
    ) -> Result<(), Error> {
        for (&bit, &column) in value.to_bits().iter().zip(&self.config.bits) {
            region.assign_advice(|| "bit column", column, offset, || Ok(F::from(bit)))?;
        }
        Ok(())
    }
}
