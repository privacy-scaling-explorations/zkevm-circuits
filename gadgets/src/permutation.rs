//! Chip that implements permutation fingerprints
//! fingerprints &= \prod_{row_j} \left ( \alpha - \sum_k (\gamma^k \cdot cell_j(k))  \right )
//! power of gamma are defined in columns to trade more columns with less degrees
use std::iter;
#[rustfmt::skip]
// | q_row_non_first | q_row_enable | q_row_last | alpha     | gamma     | gamma power 2   | ... | row fingerprint | accmulated fingerprint |
// |-----------------|--------------|------------|-----------|-----------|-----------------|     | --------------- | ---------------------- |
// | 0               |1             |0           |alpha      | gamma     | gamma **2       | ... |  F              |  F                     |
// | 1               |1             |0           |alpha      | gamma     | gamma **2       | ... |  F              |  F                     |
// | 1               |1             |1           |alpha      | gamma     | gamma **2       | ... |  F              |  F                     |

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
    /// acc_fingerprints
    pub acc_fingerprints: Column<Advice>,
    row_fingerprints: Column<Advice>,
    alpha: Column<Advice>,
    power_of_gamma: Vec<Column<Advice>>,
    // selector
    q_row_non_first: Selector, // 1 between (first, end], exclude first
    q_row_enable: Selector,    // 1 for all rows (including first)
    /// q_row_last
    pub q_row_last: Selector, // 1 in the last row

    _phantom: PhantomData<F>,

    acc_fingerprints_cur_expr: Expression<F>,
}

/// (alpha, gamma, row_fingerprints_prev_cell, row_fingerprints_next_cell, prev_acc_fingerprints,
/// next_acc_fingerprints)
type PermutationAssignedCells<F> = (
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
);

impl<F: Field> PermutationChipConfig<F> {
    /// assign
    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        alpha: Value<F>,
        gamma: Value<F>,
        acc_fingerprints_prev: Value<F>,
        col_values: &[Vec<Value<F>>],
        prefix: &'static str,
    ) -> Result<PermutationAssignedCells<F>, Error> {
        self.annotate_columns_in_region(region, prefix);

        // get accumulated fingerprints of each row
        let fingerprints =
            get_permutation_fingerprints(col_values, alpha, gamma, acc_fingerprints_prev);

        // power_of_gamma start from gamma**1
        let power_of_gamma = {
            let num_of_col = col_values.get(0).map(|row| row.len()).unwrap_or_default();
            std::iter::successors(Some(gamma), |prev| (*prev * gamma).into())
                .take(num_of_col.saturating_sub(1))
                .collect::<Vec<Value<F>>>()
        };

        let mut alpha_first_cell = None;
        let mut gamma_first_cell = None;
        let mut acc_fingerprints_prev_cell = None;
        let mut acc_fingerprints_next_cell = None;

        let mut row_fingerprints_prev_cell = None;
        let mut row_fingerprints_next_cell = None;

        for (offset, (row_acc_fingerprints, row_fingerprints)) in fingerprints.iter().enumerate() {
            // skip first fingerprint for its prev_fingerprint
            if offset != 0 {
                self.q_row_non_first.enable(region, offset)?;
            }

            self.q_row_enable.enable(region, offset)?;

            let row_acc_fingerprint_cell = region.assign_advice(
                || format!("acc_fingerprints at index {}", offset),
                self.acc_fingerprints,
                offset,
                || *row_acc_fingerprints,
            )?;

            let row_fingerprints_cell = region.assign_advice(
                || format!("row_fingerprints at index {}", offset),
                self.row_fingerprints,
                offset,
                || *row_fingerprints,
            )?;

            let alpha_cell = region.assign_advice(
                || format!("alpha at index {}", offset),
                self.alpha,
                offset,
                || alpha,
            )?;
            let gamma_cells = self
                .power_of_gamma
                .iter()
                .zip_eq(power_of_gamma.iter())
                .map(|(col, value)| {
                    region.assign_advice(
                        || format!("gamma at index {}", offset),
                        *col,
                        offset,
                        || *value,
                    )
                })
                .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;

            if offset == 0 {
                alpha_first_cell = Some(alpha_cell);
                gamma_first_cell = Some(gamma_cells[0].clone());
                acc_fingerprints_prev_cell = Some(row_acc_fingerprint_cell.clone());
                row_fingerprints_prev_cell = Some(row_fingerprints_cell.clone())
            }
            // last offset
            if offset == fingerprints.len() - 1 {
                self.q_row_last.enable(region, offset)?;
                acc_fingerprints_next_cell = Some(row_acc_fingerprint_cell);
                row_fingerprints_next_cell = Some(row_fingerprints_cell)
            }
        }

        Ok((
            alpha_first_cell.unwrap(),
            gamma_first_cell.unwrap(),
            row_fingerprints_prev_cell.unwrap(),
            row_fingerprints_next_cell.unwrap(),
            acc_fingerprints_prev_cell.unwrap(),
            acc_fingerprints_next_cell.unwrap(),
        ))
    }

    /// Annotates columns of this gadget embedded within a circuit region.
    pub fn annotate_columns_in_region(&self, region: &mut Region<F>, prefix: &str) {
        [
            (
                self.acc_fingerprints,
                "GADGETS_PermutationChipConfig_acc_fingerprints".to_string(),
            ),
            (
                self.row_fingerprints,
                "GADGETS_PermutationChipConfig_row_fingerprints".to_string(),
            ),
            (
                self.alpha,
                "GADGETS_PermutationChipConfig_alpha".to_string(),
            ),
        ]
        .iter()
        .cloned()
        .chain(self.power_of_gamma.iter().enumerate().map(|(i, col)| {
            (
                *col,
                format!("GADGETS_PermutationChipConfig_gamma_{}", i + 1),
            )
        }))
        .for_each(|(col, ann)| region.name_column(|| format!("{}_{}", prefix, ann), col));
    }

    /// acc_fingerprints_cur_expr
    pub fn acc_fingerprints_cur_expr(&self) -> Expression<F> {
        self.acc_fingerprints_cur_expr.clone()
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
        let acc_fingerprints = meta.advice_column();
        let row_fingerprints = meta.advice_column();
        let alpha = meta.advice_column();

        // trade more columns with less degrees
        let power_of_gamma = (0..cols.len() - 1)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>(); // first element is gamma**1

        let q_row_non_first = meta.selector();
        let q_row_enable = meta.selector();
        let q_row_last = meta.selector();

        meta.enable_equality(acc_fingerprints);
        meta.enable_equality(alpha);
        meta.enable_equality(power_of_gamma[0]);

        let mut acc_fingerprints_cur_expr: Expression<F> = 0.expr();

        meta.create_gate(
            "acc_fingerprints_cur = acc_fingerprints_prev * row_fingerprints_cur",
            |meta| {
                let q_row_non_first = meta.query_selector(q_row_non_first);
                let acc_fingerprints_prev = meta.query_advice(acc_fingerprints, Rotation::prev());
                let acc_fingerprints_cur = meta.query_advice(acc_fingerprints, Rotation::cur());
                let row_fingerprints_cur = meta.query_advice(row_fingerprints, Rotation::cur());

                acc_fingerprints_cur_expr = acc_fingerprints_cur.clone();

                [q_row_non_first
                    * (acc_fingerprints_cur - acc_fingerprints_prev * row_fingerprints_cur)]
            },
        );

        meta.create_gate(
            "row_fingerprints_cur = fingerprints(column_exprs)",
            |meta| {
                let alpha = meta.query_advice(alpha, Rotation::cur());
                let row_fingerprints_cur = meta.query_advice(row_fingerprints, Rotation::cur());
                let power_of_gamma = iter::once(1.expr())
                    .chain(
                        power_of_gamma
                            .iter()
                            .map(|column| meta.query_advice(*column, Rotation::cur())),
                    )
                    .collect::<Vec<Expression<F>>>();

                let q_row_enable = meta.query_selector(q_row_enable);
                let cols_cur_exprs = cols
                    .iter()
                    .map(|col| meta.query_advice(*col, Rotation::cur()))
                    .collect::<Vec<Expression<F>>>();

                let perf_term = cols_cur_exprs
                    .iter()
                    .zip_eq(power_of_gamma.iter())
                    .map(|(a, b)| a.clone() * b.clone())
                    .fold(0.expr(), |a, b| a + b);
                [q_row_enable * (row_fingerprints_cur - (alpha - perf_term))]
            },
        );

        meta.create_gate("challenges consistency", |meta| {
            let q_row_non_first = meta.query_selector(q_row_non_first);
            let alpha_prev = meta.query_advice(alpha, Rotation::prev());
            let alpha_cur = meta.query_advice(alpha, Rotation::cur());

            [
                vec![q_row_non_first.clone() * (alpha_prev - alpha_cur)],
                power_of_gamma
                    .iter()
                    .map(|col| {
                        let gamma_prev = meta.query_advice(*col, Rotation::prev());
                        let gamma_cur = meta.query_advice(*col, Rotation::cur());
                        q_row_non_first.clone() * (gamma_prev - gamma_cur)
                    })
                    .collect(),
            ]
            .concat()
        });

        meta.create_gate("power of gamma", |meta| {
            let q_row_non_first = meta.query_selector(q_row_non_first);
            let gamma = meta.query_advice(power_of_gamma[0], Rotation::cur());
            power_of_gamma
                .iter()
                .tuple_windows()
                .map(|(col1, col2)| {
                    let col1_cur = meta.query_advice(*col1, Rotation::cur());
                    let col2_cur = meta.query_advice(*col2, Rotation::cur());
                    q_row_non_first.clone() * (col2_cur - col1_cur * gamma.clone())
                })
                .collect::<Vec<Expression<F>>>()
        });

        PermutationChipConfig {
            acc_fingerprints,
            acc_fingerprints_cur_expr,
            row_fingerprints,
            q_row_non_first,
            q_row_enable,
            q_row_last,
            alpha,
            power_of_gamma,
            _phantom: PhantomData::<F> {},
        }
    }
}

impl<F: Field> PermutationChip<F> {}

/// get permutation fingerprint of rows
pub fn get_permutation_fingerprints<F: Field>(
    col_values: &[Vec<Value<F>>],
    alpha: Value<F>,
    gamma: Value<F>,
    acc_fingerprints_prev: Value<F>,
) -> Vec<(Value<F>, Value<F>)> {
    let power_of_gamma = {
        let num_of_col = col_values.get(0).map(|row| row.len()).unwrap_or_default();
        std::iter::successors(Some(Value::known(F::ONE)), |prev| (*prev * gamma).into())
            .take(num_of_col)
            .collect::<Vec<Value<F>>>()
    };
    let mut result = vec![];
    col_values
        .iter()
        .map(|row| {
            let tmp = row
                .iter()
                .zip_eq(power_of_gamma.iter())
                .map(|(a, b)| *a * b)
                .fold(Value::known(F::ZERO), |prev, cur| prev + cur);
            alpha - tmp
        })
        .enumerate()
        .for_each(|(i, value)| {
            if i == 0 {
                result.push((acc_fingerprints_prev, value));
            } else {
                result.push((result[result.len() - 1].0 * value, value));
            }
        });
    result
}
