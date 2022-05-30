use crate::{
    evm_circuit::{
        table::RwTableTag,
        util::{and, not},
    },
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;
use strum::EnumCount;

// TODO: rename to as_bits
pub trait AsBits<const N: usize> {
    fn as_bits(&self) -> [bool; N];
}

impl AsBits<4> for RwTableTag {
    fn as_bits(&self) -> [bool; 4] {
        let mut bits = [false; 4];
        let mut x = *self as u8;
        for i in 0..4 {
            bits[3 - i] = x % 2 == 1;
            x /= 2;
        }
        bits
    }
}

impl<const N: usize> AsBits<N> for usize {
    fn as_bits(&self) -> [bool; N] {
        let mut bits = [false; N];
        let mut x = *self as u64;
        for i in 0..N {
            bits[N - 1 - i] = x % 2 == 1;
            x /= 2;
        }
        bits
    }
}

#[derive(Clone, Copy)]
pub struct Config<T, const N: usize>
where
    T: AsBits<N>,
{
    pub bits: [Column<Advice>; N],
    _marker: PhantomData<T>,
}

impl<T, const N: usize> Config<T, N>
where
    T: AsBits<N>,
{
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: RwTableTag,
    ) -> Result<(), Error> {
        for (&column, &bit) in self.bits.iter().zip(&value.as_bits()) {
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
        move |meta: &mut VirtualCells<'_, F>| {
            let bits = self.bits.map(|bit| meta.query_advice(bit, rotation));
            bits.iter()
                .fold(0.expr(), |result, bit| bit.clone() + result * 2.expr())
        }
    }

    pub fn value_equals<F: Field, S: AsBits<N>>(
        &self,
        value: &S,
        rotation: Rotation,
    ) -> impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F> + '_ {
        let bits = value.as_bits();
        move |meta: &mut VirtualCells<'_, F>| {
            and::expr(
                bits.iter()
                    .zip(&self.bits.map(|bit| meta.query_advice(bit, rotation)))
                    .map(|(&bit, query)| {
                        if bit {
                            query.clone()
                        } else {
                            not::expr(query.clone())
                        }
                    }),
            )
        }
    }
}

pub struct Chip<F: Field, T, const N: usize>
where
    T: AsBits<N>,
{
    config: Config<T, N>,
    _marker: PhantomData<F>,
}

impl<F: Field, T: EnumCount, const N: usize> Chip<F, T, N>
where
    T: AsBits<N>,
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

        let config = Config {
            bits,
            _marker: PhantomData,
        };

        for i in T::COUNT..T::COUNT.next_power_of_two() {
            meta.create_gate("binary number value in range", |meta| {
                let selector = meta.query_fixed(selector, Rotation::cur());
                let value_equals_i = config.value_equals(&i, Rotation::cur());
                vec![selector * value_equals_i(meta)]
            })
        }

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: RwTableTag,
    ) -> Result<(), Error> {
        for (&bit, &column) in value.as_bits().iter().zip(&self.config.bits) {
            region.assign_advice(|| "bit column", column, offset, || Ok(F::from(bit)))?;
        }
        Ok(())
    }
}
