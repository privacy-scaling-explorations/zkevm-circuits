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
use std::collections::BTreeSet;
use std::marker::PhantomData;
use strum::IntoEnumIterator;

pub trait AsBits<const N: usize> {
    // Return the bits of self, starting from the most significant.
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
pub struct Config<T, const N: usize> {
    // Must be constrained to be binary for correctness.
    pub bits: [Column<Advice>; N],
    _marker: PhantomData<T>,
}

impl<T, const N: usize> Config<T, N>
where
    T: AsBits<N>,
{
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
        value: S,
        rotation: Rotation,
    ) -> impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F> {
        let bits = self.bits;
        move |meta| Self::value_equals_expr(value, bits.map(|bit| meta.query_advice(bit, rotation)))
    }

    // Returns an expression that evaluates to 1 if expressions are equal to value
    // as bits. The returned expression is of degree N.
    pub fn value_equals_expr<F: Field, S: AsBits<N>>(
        value: S,
        expressions: [Expression<F>; N], // must be binary.
    ) -> Expression<F> {
        and::expr(
            value
                .as_bits()
                .iter()
                .zip(&expressions)
                .map(|(&bit, expression)| {
                    if bit {
                        expression.clone()
                    } else {
                        not::expr(expression.clone())
                    }
                }),
        )
    }
}

// This chip helps working with binary encoding of integers of length N bits by:
//  - enforcing that the binary representation is in the valid range defined by
//    T.
//  - creating expressions (via the Config) that evaluate to 1 when the bits
//    match a specific value and 0 otherwise.
pub struct Chip<F: Field, T, const N: usize> {
    config: Config<T, N>,
    _marker: PhantomData<F>,
}

impl<F: Field, T: IntoEnumIterator, const N: usize> Chip<F, T, N>
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

        // Disallow bit patterns (if any) that don't correspond to a variant of T.
        let valid_values: BTreeSet<usize> = T::iter().map(|t| from_bits(&t.as_bits())).collect();
        let mut invalid_values = (0..1 << N).filter(|i| !valid_values.contains(i)).peekable();
        if invalid_values.peek().is_some() {
            meta.create_gate("binary number value in range", |meta| {
                let selector = meta.query_fixed(selector, Rotation::cur());
                invalid_values
                    .map(|i| {
                        let value_equals_i = config.value_equals(i, Rotation::cur());
                        selector.clone() * value_equals_i(meta)
                    })
                    .collect::<Vec<_>>()
            });
        }

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: &T,
    ) -> Result<(), Error> {
        for (&bit, &column) in value.as_bits().iter().zip(&self.config.bits) {
            region.assign_advice(
                || format!("binary number {:?}", column),
                column,
                offset,
                || Ok(F::from(bit)),
            )?;
        }
        Ok(())
    }
}

pub fn from_bits(bits: &[bool]) -> usize {
    bits.iter()
        .fold(0, |result, &bit| bit as usize + 2 * result)
}
