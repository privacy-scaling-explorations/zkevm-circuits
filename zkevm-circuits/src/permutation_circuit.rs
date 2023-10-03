use std::marker::PhantomData;

use eth_types::Field;
use gadgets::util::Expr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector},
    poly::Rotation,
};
use itertools::Itertools;

use crate::{
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness,
};

/// Config for PermutationCircuit
#[derive(Clone, Debug)]
pub struct PermutationCircuitConfig<F: Field> {
    // column
    fingerprints: Column<Advice>,
    alpha: Column<Advice>,
    gamma: Column<Advice>,
    permutation_instance: Column<Instance>,

    // selector
    q_row_non_first: Selector, // 1 between (first, last], exclude first

    _phantom: PhantomData<F>,
}

/// Circuit configuration arguments
pub struct PermutationCircuitConfigArgs {
    pub cols: Vec<Column<Advice>>,
}

impl<F: Field> SubCircuitConfig<F> for PermutationCircuitConfig<F> {
    type ConfigArgs = PermutationCircuitConfigArgs;

    /// Return a new TxCircuitConfig
    fn new(meta: &mut ConstraintSystem<F>, Self::ConfigArgs { cols }: Self::ConfigArgs) -> Self {
        let fingerprints = meta.advice_column();
        let permutation_instance = meta.instance_column();
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
                q_row_non_first * (alpha_prev - alpha_cur),
                q_row_non_first * (gamma_prev - gamma_cur),
            ]
        });
        Self {
            fingerprints,
            permutation_instance,
            q_row_non_first,
            alpha,
            gamma,
            _phantom: PhantomData::<F> {},
        }
    }
}

impl<F: Field> PermutationCircuitConfig<F> {
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
        // Constrain raw_public_input cells to public inputs
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
            self.q_row_non_first.enable(region, offset);

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

    /// Get number of rows required.
    pub fn get_num_rows_required(num_rw: usize) -> usize {
        unimplemented!()
    }
}

/// permutation fingerprint gadget
#[derive(Debug, Clone)]
pub struct PermutationCircuit<F> {
    alpha: Value<F>,
    gamma: Value<F>,
    prev_continuous_fingerprint: Value<F>,
    col_values: Vec<Vec<Value<F>>>,
}

impl<F: Field> SubCircuit<F> for PermutationCircuit<F> {
    type Config = PermutationCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn new_from_block(_block: &witness::Block<F>) -> Self {
        unimplemented!()
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        unimplemented!()
    }

    /// Make the assignments to the TxCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let (alpha_cell, gamma_cell, prev_continuous_fingerprint_cell, new_fingerprint_cell) =
            layouter.assign_region(
                || "permutation circuit",
                |mut region| {
                    let cells = config.assign(
                        &mut region,
                        self.alpha,
                        self.gamma,
                        self.prev_continuous_fingerprint,
                        &self.col_values,
                    )?;

                    Ok(cells)
                },
            )?;
        layouter.constrain_instance(alpha_cell.cell(), config.permutation_instance, 0)?;
        layouter.constrain_instance(gamma_cell.cell(), config.permutation_instance, 1)?;
        layouter.constrain_instance(
            prev_continuous_fingerprint_cell.cell(),
            config.permutation_instance,
            2,
        )?;
        layouter.constrain_instance(new_fingerprint_cell.cell(), config.permutation_instance, 2)?;

        Ok(())
    }

    /// Compute the public inputs for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        // TODO
        unimplemented!()
    }
}

impl<F: Field> PermutationCircuit<F> {}
