use std::convert::TryInto;

use crate::{evm_circuit::param::N_BYTES_MEMORY_ADDRESS, util::Expr};
use eth_types::U256;
use halo2::{
    arithmetic::FieldExt,
    circuit::{self, Region},
    plonk::{
        Advice, Assigned, Column, ConstraintSystem, Error, Expression,
        VirtualCells,
    },
    poly::Rotation,
};

use super::table::Table;

pub(crate) mod common_gadget;
pub(crate) mod constraint_builder;
pub(crate) mod math_gadget;
pub(crate) mod memory_gadget;

type Address = u64;
type MemorySize = u64;

#[derive(Clone, Debug)]
pub(crate) struct Cell<F> {
    // expression for constraint
    expression: Expression<F>,
    column: Column<Advice>,
    // relative position to selector for synthesis
    rotation: usize,
}

impl<F: FieldExt> Cell<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        rotation: usize,
    ) -> Self {
        Self {
            expression: meta.query_advice(column, Rotation(rotation as i32)),
            column,
            rotation,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<circuit::Cell, Error> {
        region.assign_advice(
            || {
                format!(
                    "Cell column: {:?} and rotation: {}",
                    self.column, self.rotation
                )
            },
            self.column,
            offset + self.rotation,
            || value.ok_or(Error::Synthesis),
        )
    }
}

impl<F: FieldExt> Expr<F> for Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

impl<F: FieldExt> Expr<F> for &Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

pub(crate) fn random_linear_combine<F: FieldExt>(
    expressions: Vec<Expression<F>>,
    power_of_randomness: &[Expression<F>],
) -> Expression<F> {
    assert!(expressions.len() <= power_of_randomness.len() + 1);

    let mut rlc = expressions[0].clone();
    for (expr, randomness) in
        expressions[1..].iter().zip(power_of_randomness.iter())
    {
        rlc = rlc + expr.clone() * randomness.clone();
    }
    rlc
}

#[derive(Clone, Debug)]
pub(crate) struct RandomLinearCombination<F, const N: usize> {
    // random linear combination expression of cells
    expression: Expression<F>,
    // inner cells in little-endian for synthesis
    pub(crate) cells: [Cell<F>; N],
}

impl<F: FieldExt, const N: usize> RandomLinearCombination<F, N> {
    const NUM_BYTES: usize = N;

    pub(crate) fn random_linear_combine(bytes: [u8; N], randomness: F) -> F {
        bytes.iter().rev().fold(F::zero(), |acc, byte| {
            acc * randomness + F::from(*byte as u64)
        })
    }

    pub(crate) fn random_linear_combine_expr(
        bytes: [Expression<F>; N],
        power_of_randomness: &[Expression<F>],
    ) -> Expression<F> {
        assert!(bytes.len() <= power_of_randomness.len() + 1);

        let mut rlc = bytes[0].clone();
        for (byte, randomness) in
            bytes[1..].iter().zip(power_of_randomness.iter())
        {
            rlc = rlc + byte.clone() * randomness.clone();
        }
        rlc
    }

    pub(crate) fn new(
        cells: [Cell<F>; N],
        power_of_randomness: &[Expression<F>],
    ) -> Self {
        Self {
            expression: Self::random_linear_combine_expr(
                cells.clone().map(|cell| cell.expr()),
                power_of_randomness,
            ),
            cells,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: Option<[u8; N]>,
    ) -> Result<Vec<circuit::Cell>, Error> {
        bytes.map_or(Err(Error::Synthesis), |bytes| {
            self.cells
                .iter()
                .zip(bytes.iter())
                .map(|(cell, byte)| {
                    cell.assign(region, offset, Some(F::from(*byte as u64)))
                })
                .collect()
        })
    }
}

impl<F: FieldExt, const N: usize> Expr<F> for RandomLinearCombination<F, N> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

pub(crate) type Word<F> = RandomLinearCombination<F, 32>;
pub(crate) type MemoryAddress<F> =
    RandomLinearCombination<F, N_BYTES_MEMORY_ADDRESS>;

/// Returns the sum of the passed in cells
pub(crate) mod sum {
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt, E: Expr<F>, I: IntoIterator<Item = E>>(
        inputs: I,
    ) -> Expression<F> {
        inputs
            .into_iter()
            .fold(0.expr(), |acc, input| acc + input.expr())
    }

    pub(crate) fn value<F: FieldExt>(values: &[u8]) -> F {
        values
            .iter()
            .fold(F::zero(), |acc, value| acc + F::from(*value as u64))
    }
}

/// Returns `1` when `expr[0] && expr[1] && ... == 1`, and returns `0`
/// otherwise. Inputs need to be boolean
pub(crate) mod and {
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt, E: Expr<F>, I: IntoIterator<Item = E>>(
        inputs: I,
    ) -> Expression<F> {
        let mut result = 1.expr();
        for (idx, input) in inputs.into_iter().enumerate() {
            result = if idx == 0 {
                input.expr()
            } else {
                result * input.expr()
            };
        }
        result
    }

    pub(crate) fn value<F: FieldExt>(inputs: Vec<F>) -> F {
        inputs.iter().fold(F::one(), |acc, input| acc * input)
    }
}

/// Returns `when_true` when `selector == 1`, and returns `when_false` when
/// `selector == 0`. `selector` needs to be boolean.
pub(crate) mod select {
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(
        selector: Expression<F>,
        when_true: Expression<F>,
        when_false: Expression<F>,
    ) -> Expression<F> {
        selector.clone() * when_true + (1.expr() - selector) * when_false
    }

    pub(crate) fn value<F: FieldExt>(
        selector: F,
        when_true: F,
        when_false: F,
    ) -> F {
        selector * when_true + (F::one() - selector) * when_false
    }

    pub(crate) fn value_word<F: FieldExt>(
        selector: F,
        when_true: [u8; 32],
        when_false: [u8; 32],
    ) -> [u8; 32] {
        if selector == F::one() {
            when_true
        } else {
            when_false
        }
    }
}

/// Decodes a field element from its byte representation
pub(crate) mod from_bytes {
    use crate::{evm_circuit::param::MAX_N_BYTES_INTEGER, util::Expr};
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt, E: Expr<F>>(bytes: &[E]) -> Expression<F> {
        assert!(
            bytes.len() <= MAX_N_BYTES_INTEGER,
            "Too many bytes to compose an integer in field"
        );
        let mut value = 0.expr();
        let mut multiplier = F::one();
        for byte in bytes.iter() {
            value = value + byte.expr() * multiplier;
            multiplier *= F::from(256);
        }
        value
    }

    pub(crate) fn value<F: FieldExt>(bytes: &[u8]) -> F {
        assert!(
            bytes.len() <= MAX_N_BYTES_INTEGER,
            "Too many bytes to compose an integer in field"
        );
        let mut value = F::zero();
        let mut multiplier = F::one();
        for byte in bytes.iter() {
            value += F::from(*byte as u64) * multiplier;
            multiplier *= F::from(256);
        }
        value
    }
}

/// Returns 2**by as FieldExt
pub(crate) fn pow_of_two<F: FieldExt>(by: usize) -> F {
    F::from(2).pow(&[by as u64, 0, 0, 0])
}

/// Returns 2**by as Expression
pub(crate) fn pow_of_two_expr<F: FieldExt>(by: usize) -> Expression<F> {
    Expression::Constant(pow_of_two(by))
}

/// Returns tuple consists of low and high part of U256
pub(crate) fn split_u256(value: &U256) -> (U256, U256) {
    (
        U256([value.0[0], value.0[1], 0, 0]),
        U256([value.0[2], value.0[3], 0, 0]),
    )
}

pub struct CachedRegion<'r, 'b, F: FieldExt> {
    region: &'r mut Region<'b, F>,
    advice: Vec<Vec<F>>,
    power_of_randomness: [F; 31],
    width_start: usize,
    height_start: usize,
}

impl<'r, 'b, F: FieldExt> CachedRegion<'r, 'b, F> {
    /// New cached region
    pub(crate) fn new(
        region: &'r mut Region<'b, F>,
        power_of_randomness: [F; 31],
        width: usize,
        height: usize,
        width_start: usize,
        height_start: usize,
    ) -> Self {
        Self {
            region,
            advice: vec![vec![F::zero(); height]; width],
            power_of_randomness,
            width_start,
            height_start,
        }
    }

    /// Assign an advice column value (witness).
    pub fn assign_advice<'v, V, VR, A, AR>(
        &'v mut self,
        annotation: A,
        column: Column<Advice>,
        offset: usize,
        mut to: V,
    ) -> Result<circuit::Cell, Error>
    where
        V: FnMut() -> Result<VR, Error> + 'v,
        VR: Into<Assigned<F>>,
        A: Fn() -> AR,
        AR: Into<String>,
    {
        // Cache the value
        let value: F = to().unwrap().into().evaluate();
        self.advice[column.index() - self.width_start]
            [offset - self.height_start] = value;

        // Actually set the value
        self.region.assign_advice(annotation, column, offset, to)
    }

    pub fn get_fixed(
        &self,
        _row_index: usize,
        _column_index: usize,
        _rotation: Rotation,
    ) -> F {
        unimplemented!("fixed column");
    }

    pub fn get_advice(
        &self,
        row_index: usize,
        column_index: usize,
        rotation: Rotation,
    ) -> F {
        self.advice[column_index - self.width_start]
            [(((row_index - self.height_start) as i32) + rotation.0) as usize]
    }

    pub fn get_instance(
        &self,
        _row_index: usize,
        column_index: usize,
        _rotation: Rotation,
    ) -> F {
        self.power_of_randomness[column_index]
    }
}

#[derive(Debug, Clone)]
pub struct IntermediateResult<F> {
    cell_type: CellType,
    cell: Cell<F>,
    expr: Expression<F>,
}

impl<F: FieldExt> IntermediateResult<F> {
    pub fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
    ) -> Result<circuit::Cell, Error> {
        let value = self.expr.evaluate(
            &|scalar| scalar,
            &|_| panic!("virtual selectors are removed during optimization"),
            &|_, column_index, rotation| {
                region.get_fixed(offset, column_index, rotation)
            },
            &|_, column_index, rotation| {
                region.get_advice(offset, column_index, rotation)
            },
            &|_, column_index, rotation| {
                region.get_instance(offset, column_index, rotation)
            },
            &|a| -a,
            &|a, b| a + b,
            &|a, b| a * b,
            &|a, scalar| a * scalar,
        );
        //println!("Intermediate result: {:?}", value);
        self.cell.assign(region, offset, Some(value))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum CellType {
    None,
    General,
    Lookup(Table),
}

#[derive(Clone, Debug)]
pub(crate) struct CellColumn<F> {
    pub(crate) index: usize,
    pub(crate) cell_type: CellType,
    pub(crate) num_used: usize,
    pub(crate) expr: Expression<F>,
}

#[derive(Clone, Debug)]
pub(crate) struct CellManager<F> {
    width: usize,
    height: usize,
    pub(crate) cells: Vec<Cell<F>>,
    pub(crate) columns: Vec<CellColumn<F>>,
}

impl<F: FieldExt> CellManager<F> {
    pub(crate) fn new(
        meta: &mut ConstraintSystem<F>,
        width: usize,
        height: usize,
        advices: &[Column<Advice>],
        is_next_step: bool,
    ) -> Self {
        assert_eq!(advices.len(), width);
        let offset = if is_next_step { height } else { 0 };
        let mut cells = Vec::with_capacity(height * width);
        let mut columns = Vec::with_capacity(height);
        meta.create_gate("Query rows for step", |meta| {
            for c in 0..width {
                for r in 0..height {
                    cells.push(Cell::new(meta, advices[c], offset + r));
                }
                columns.push(CellColumn {
                    index: c,
                    cell_type: CellType::None,
                    num_used: 0,
                    expr: cells[c * height].expr(),
                });
            }
            vec![0.expr()]
        });

        Self {
            width,
            height,
            cells,
            columns,
        }
    }

    pub(crate) fn query_cells(
        &mut self,
        cell_type: CellType,
        count: usize,
    ) -> Vec<Cell<F>> {
        let mut cells = Vec::with_capacity(count);
        while cells.len() < count {
            let column_idx = self.find_column(cell_type);
            let column = &mut self.columns[column_idx];
            cells.push(
                self.cells[column_idx * self.height + column.num_used].clone(),
            );
            column.num_used += 1;
        }
        cells
    }

    pub(crate) fn query_cell(&mut self, cell_type: CellType) -> Cell<F> {
        let cells = self.query_cells(cell_type, 1);
        cells[0].clone()
    }

    fn find_column(&mut self, cell_type: CellType) -> usize {
        for column in self.columns.iter_mut() {
            if (column.cell_type == cell_type
                || column.cell_type == CellType::None)
                && column.num_used < self.height
            {
                column.cell_type = cell_type;
                return column.index;
            }
        }
        unreachable!("not enough cells for query")
    }
}
