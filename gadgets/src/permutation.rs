//! Chip that implements permutation fingerprints
//! fingerprints &= \prod_{row_j} \left ( \alpha - \sum_k (\gamma^k \cdot cell_j(k))  \right )
#[rustfmt::skip]
// | q_row_non_first | alpha     | gamma     | fingerprints    |
// |-----------------|-----------|-----------|-----------------|
// | 0               | alpha     | gamma     | fingerprints_0  |
// | 1               | alpha     | gamma     | fingerprints_1  |
// | 1               | alpha     | gamma     | fingerprints_2  |

use std::marker::PhantomData;

use crate::util::Expr;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;

/// Config for PermutationChipConfig
#[derive(Clone, Debug)]
pub struct PermutationChipConfig<F> {
    // column
    fingerprints: Column<Advice>,
    alpha: Column<Advice>,
    gamma: Column<Advice>,
    // selector
    q_row_non_first: Selector, // 1 between (first, end], exclude first

    _phantom: PhantomData<F>,
}

impl<F: Field> PermutationChipConfig<F> {
    /// assign
    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        alpha: Value<F>,
        gamma: Value<F>,
        prev_continuous_fingerprint: Value<F>,
        col_values: &Vec<Vec<Value<F>>>,
    ) -> Result<
        (
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
        let mut offset = 0;
        let alpha_first_cell = region.assign_advice(
            || format!("alpha at index {}", offset),
            self.alpha,
            offset,
            || alpha,
        )?;
        let gamma_first_cell = region.assign_advice(
            || format!("gamma at index {}", offset),
            self.gamma,
            offset,
            || gamma,
        )?;
        let prev_continuous_fingerprint_cell = region.assign_advice(
            || format!("fingerprint at index {}", offset),
            self.fingerprints,
            offset,
            || prev_continuous_fingerprint,
        )?;

        let power_of_gamma = {
            let num_of_col = col_values.get(0).map(|x| x.len()).unwrap_or_default();
            std::iter::successors(Some(Value::known(F::ONE)), |prev| {
                (prev.clone() * gamma.clone()).into()
            })
            .take(num_of_col)
            .collect::<Vec<Value<F>>>()
        };

        offset += 1;

        let mut last_fingerprint_cell = None;
        for (_, row) in col_values.iter().enumerate() {
            self.q_row_non_first.enable(region, offset)?;

            let perf_term = {
                let tmp = row
                    .iter()
                    .zip_eq(power_of_gamma.iter())
                    .map(|(a, b)| a.zip(*b).map(|(a, b)| a * b))
                    .fold(Value::known(F::ZERO), |prev, cur| {
                        prev.zip(cur).map(|(a, b)| a + b)
                    });
                alpha.zip(tmp).map(|(alpha, perf_term)| alpha - perf_term)
            };
            let fingerprint_cell = region.assign_advice(
                || format!("fingerprint at index {}", offset),
                self.fingerprints,
                offset,
                || perf_term,
            )?;
            if offset == col_values.len() {
                last_fingerprint_cell = Some(fingerprint_cell);
            }
            region.assign_advice(
                || format!("alpha at index {}", offset),
                self.alpha,
                offset,
                || alpha,
            )?;
            region.assign_advice(
                || format!("gamma at index {}", offset),
                self.gamma,
                offset,
                || gamma,
            )?;

            offset += 1;
        }

        Ok((
            alpha_first_cell,
            gamma_first_cell,
            prev_continuous_fingerprint_cell,
            last_fingerprint_cell.unwrap(),
        ))
    }
}

/// permutation fingerprint gadget
#[derive(Debug, Clone)]
pub struct PermutationChip<F: Field> {
    /// config
    pub config: PermutationChipConfig<F>,
}

impl<F: Field> PermutationChip<F> {
    /// configure
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        cols: Vec<Column<Advice>>,
    ) -> PermutationChipConfig<F> {
        let fingerprints = meta.advice_column();
        let alpha = meta.advice_column();
        let gamma = meta.advice_column();
        let q_row_non_first = meta.selector();

        meta.create_gate("permutation fingerprint update logic", |meta| {
            let alpha = meta.query_advice(alpha, Rotation::cur());
            let gamma = meta.query_advice(gamma, Rotation::cur());
            let q_row_non_first = meta.query_selector(q_row_non_first);
            let cols_cur_exprs = cols
                .iter()
                .map(|col| meta.query_advice(*col, Rotation::cur()))
                .collect::<Vec<Expression<F>>>();
            let fingerprint_prev = meta.query_advice(fingerprints, Rotation::prev());
            let fingerprint_cur = meta.query_advice(fingerprints, Rotation::cur());

            let power_of_gamma = std::iter::successors(1.expr().into(), |prev: &Expression<F>| {
                (prev.clone() * gamma.clone()).into()
            })
            .take(cols.len())
            .collect::<Vec<Expression<F>>>();

            let perf_term = cols_cur_exprs
                .iter()
                .zip(power_of_gamma.iter())
                .map(|(a, b)| a.clone() * b.clone())
                .fold(0.expr(), |a, b| a + b);

            [q_row_non_first * (fingerprint_cur - fingerprint_prev * (alpha - perf_term))]
        });

        meta.create_gate("challenges consistency", |meta| {
            let q_row_non_first = meta.query_selector(q_row_non_first);
            let alpha_prev = meta.query_advice(alpha, Rotation::prev());
            let alpha_cur = meta.query_advice(alpha, Rotation::cur());
            let gamma_prev = meta.query_advice(gamma, Rotation::prev());
            let gamma_cur = meta.query_advice(gamma, Rotation::cur());
            [
                q_row_non_first.clone() * (alpha_prev - alpha_cur),
                q_row_non_first * (gamma_prev - gamma_cur),
            ]
        });
        PermutationChipConfig {
            fingerprints,
            q_row_non_first,
            alpha,
            gamma,
            _phantom: PhantomData::<F> {},
        }
    }
}

impl<F: Field> PermutationChip<F> {}
