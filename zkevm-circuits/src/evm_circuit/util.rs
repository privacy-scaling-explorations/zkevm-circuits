pub use crate::util::{
    query_expression,
    word::{Word, WordExpr},
    Challenges, Expr,
};
use crate::{
    evm_circuit::{
        param::{
            LOOKUP_CONFIG, N_BYTES_MEMORY_ADDRESS, N_COPY_COLUMNS, N_PHASE2_COLUMNS, N_U8_LOOKUPS,
        },
        table::Table,
    },
    util::{cell_manager::CMFixedWidthStrategyDistribution, int_decomposition::IntDecomposition},
    witness::{Block, ExecStep, Rw, RwMap},
};
use eth_types::{Address, Field, U256};
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};
use itertools::Itertools;
use std::hash::{Hash, Hasher};

pub(crate) mod common_gadget;
pub(crate) mod constraint_builder;
pub(crate) mod instrumentation;
pub(crate) mod math_gadget;
pub(crate) mod memory_gadget;
pub(crate) mod precompile_gadget;

pub use gadgets::util::{and, not, or, select, sum};

use super::param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_U64, N_U16_LOOKUPS};

#[deprecated(note = "Removing this would require to edit almost all gadget")]
pub(crate) use crate::util::cell_manager::{Cell, CellType};

pub struct CachedRegion<'r, 'b, F: Field> {
    region: &'r mut Region<'b, F>,
    advice: Vec<Vec<F>>,
    challenges: &'r Challenges<Value<F>>,
    advice_columns: Vec<Column<Advice>>,
    width_start: usize,
    height_start: usize,
}

impl<'r, 'b, F: Field> CachedRegion<'r, 'b, F> {
    /// New cached region
    pub(crate) fn new(
        region: &'r mut Region<'b, F>,
        challenges: &'r Challenges<Value<F>>,
        advice_columns: Vec<Column<Advice>>,
        height: usize,
        height_start: usize,
    ) -> Self {
        Self {
            region,
            advice: vec![vec![F::ZERO; height]; advice_columns.len()],
            challenges,
            width_start: advice_columns[0].index(),
            height_start,
            advice_columns,
        }
    }

    /// This method replicates the assignment of 1 row at height_start (which
    /// must be already assigned via the CachedRegion) into a range of rows
    /// indicated by offset_begin, offset_end. It can be used as a "quick"
    /// path for assignment for repeated padding rows.
    pub fn replicate_assignment_for_range<A, AR>(
        &mut self,
        annotation: A,
        offset_begin: usize,
        offset_end: usize,
    ) -> Result<(), Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        for (v, column) in self
            .advice
            .iter()
            .map(|values| values[0])
            .zip_eq(self.advice_columns.iter())
        {
            if v.is_zero_vartime() {
                continue;
            }
            let annotation: &String = &annotation().into();
            for offset in offset_begin..offset_end {
                self.region
                    .assign_advice(|| annotation, *column, offset, || Value::known(v))?;
            }
        }

        Ok(())
    }

    /// Assign an advice column value (witness).
    pub fn assign_advice<'v, V, VR, A, AR>(
        &'v mut self,
        annotation: A,
        column: Column<Advice>,
        offset: usize,
        to: V,
    ) -> Result<AssignedCell<VR, F>, Error>
    where
        V: Fn() -> Value<VR> + 'v,
        for<'vr> Assigned<F>: From<&'vr VR>,
        A: Fn() -> AR,
        AR: Into<String>,
    {
        // Actually set the value
        let res = self.region.assign_advice(annotation, column, offset, &to);
        // Cache the value
        // Note that the `value_field` in `AssignedCell` might be `Value::unknown` if
        // the column has different phase than current one, so we call to `to`
        // again here to cache the value.
        if res.is_ok() {
            to().map(|f| {
                self.advice[column.index() - self.width_start][offset - self.height_start] =
                    Assigned::from(&f).evaluate();
            });
        }
        res
    }

    pub fn get_fixed(&self, _row_index: usize, _column_index: usize, _rotation: Rotation) -> F {
        unimplemented!("fixed column");
    }

    pub fn get_advice(&self, row_index: usize, column_index: usize, rotation: Rotation) -> F {
        self.advice[column_index - self.width_start]
            [(((row_index - self.height_start) as i32) + rotation.0) as usize]
    }

    pub fn challenges(&self) -> &Challenges<Value<F>> {
        self.challenges
    }

    pub fn keccak_rlc(&self, le_bytes: &[u8]) -> Value<F> {
        self.challenges
            .keccak_input()
            .map(|r| rlc::value(le_bytes, r))
    }

    pub fn code_hash(&self, n: U256) -> Word<Value<F>> {
        Word::from(n).into_value()
    }

    /// Constrains a cell to have a constant value.
    ///
    /// Returns an error if the cell is in a column where equality has not been
    /// enabled.
    pub fn constrain_constant<VR>(
        &mut self,
        cell: AssignedCell<F, F>,
        constant: VR,
    ) -> Result<(), Error>
    where
        VR: Into<Assigned<F>>,
    {
        self.region.constrain_constant(cell.cell(), constant.into())
    }
}

#[derive(Debug, Clone)]
pub struct StoredExpression<F> {
    pub(crate) name: String,
    cell: Cell<F>,
    cell_type: CellType,
    expr: Expression<F>,
    expr_id: String,
}

impl<F> Hash for StoredExpression<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expr_id.hash(state);
        self.cell_type.hash(state);
    }
}

/// Evaluate an expression using a `CachedRegion` at `offset`.
pub(crate) fn evaluate_expression<F: Field>(
    expr: &Expression<F>,
    region: &CachedRegion<'_, '_, F>,
    offset: usize,
) -> Value<F> {
    expr.evaluate(
        &|scalar| Value::known(scalar),
        &|_| unimplemented!("selector column"),
        &|fixed_query| {
            Value::known(region.get_fixed(
                offset,
                fixed_query.column_index(),
                fixed_query.rotation(),
            ))
        },
        &|advice_query| {
            Value::known(region.get_advice(
                offset,
                advice_query.column_index(),
                advice_query.rotation(),
            ))
        },
        &|_| unimplemented!("instance column"),
        &|challenge| *region.challenges().indexed()[challenge.index()],
        &|a| -a,
        &|a, b| a + b,
        &|a, b| a * b,
        &|a, scalar| a * Value::known(scalar),
    )
}

impl<F: Field> StoredExpression<F> {
    pub fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
    ) -> Result<Value<F>, Error> {
        let value = evaluate_expression(&self.expr, region, offset);
        self.cell.assign(region, offset, value)?;
        Ok(value)
    }
}

//
#[allow(clippy::mut_range_bound)]
pub(crate) fn evm_cm_distribute_advice<F: Field>(
    meta: &mut ConstraintSystem<F>,
    advices: &[Column<Advice>],
) -> CMFixedWidthStrategyDistribution {
    let mut dist = CMFixedWidthStrategyDistribution::default();

    let mut column_idx = 0;
    // Mark columns used for lookups in Phase3
    for &(table, count) in LOOKUP_CONFIG {
        for _ in 0usize..count {
            dist.add(CellType::Lookup(table), advices[column_idx]);
            column_idx += 1;
        }
    }

    // Mark columns used for Phase2 constraints
    for _ in 0..N_PHASE2_COLUMNS {
        dist.add(CellType::StoragePhase2, advices[column_idx]);
        column_idx += 1;
    }

    // Mark columns used for copy constraints
    for _ in 0..N_COPY_COLUMNS {
        meta.enable_equality(advices[column_idx]);
        dist.add(CellType::StoragePermutation, advices[column_idx]);
        column_idx += 1;
    }

    // Mark columns used for byte lookup
    #[allow(clippy::reversed_empty_ranges)]
    for _ in 0..N_U8_LOOKUPS {
        dist.add(CellType::Lookup(Table::U8), advices[column_idx]);
        assert_eq!(advices[column_idx].column_type().phase(), 0);
        column_idx += 1;
    }

    // Mark columns used for byte lookup
    #[allow(clippy::reversed_empty_ranges)]
    for _ in 0..N_U16_LOOKUPS {
        dist.add(CellType::Lookup(Table::U16), advices[column_idx]);
        assert_eq!(advices[column_idx].column_type().phase(), 0);
        column_idx += 1;
    }

    // Mark columns used for for Phase1 constraints
    for _ in column_idx..advices.len() {
        dist.add(CellType::StoragePhase1, advices[column_idx]);
        column_idx += 1;
    }

    dist
}

#[derive(Clone, Debug)]
pub struct RandomLinearCombination<F, const N: usize> {
    // random linear combination expression of cells
    expression: Expression<F>,
    // inner cells in little-endian for synthesis
    pub(crate) cells: [Cell<F>; N],
}

impl<F: Field, const N: usize> RandomLinearCombination<F, N> {
    /// XXX for randomness 256.expr(), consider using IntDecomposition instead
    pub(crate) fn new(cells: [Cell<F>; N], randomness: Expression<F>) -> Self {
        Self {
            expression: rlc::expr(&cells.clone().map(|cell| cell.expr()), randomness),
            cells,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: Option<[u8; N]>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        bytes.map_or(Err(Error::Synthesis), |bytes| {
            self.cells
                .iter()
                .zip(bytes.iter())
                .map(|(cell, byte)| {
                    cell.assign(region, offset, Value::known(F::from(*byte as u64)))
                })
                .collect()
        })
    }
}

impl<F: Field, const N: usize> Expr<F> for RandomLinearCombination<F, N> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

pub(crate) type MemoryAddress<F> = IntDecomposition<F, N_BYTES_MEMORY_ADDRESS>;

pub(crate) type AccountAddress<F> = IntDecomposition<F, N_BYTES_ACCOUNT_ADDRESS>;

pub(crate) type U64Cell<F> = IntDecomposition<F, N_BYTES_U64>;

/// Decodes a field element from its byte representation in little endian order
pub(crate) mod from_bytes {
    use crate::{evm_circuit::param::MAX_N_BYTES_INTEGER, util::Expr};
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field, E: Expr<F>>(bytes: &[E]) -> Expression<F> {
        debug_assert!(
            bytes.len() <= MAX_N_BYTES_INTEGER,
            "Too many bytes to compose an integer in field"
        );
        let mut value = 0.expr();
        let mut multiplier = F::ONE;
        for byte in bytes.iter() {
            value = value + byte.expr() * multiplier;
            multiplier *= F::from(256);
        }
        value
    }

    pub(crate) fn value<F: Field>(bytes: &[u8]) -> F {
        debug_assert!(
            bytes.len() <= MAX_N_BYTES_INTEGER,
            "Too many bytes to compose an integer in field"
        );
        let mut value = F::ZERO;
        let mut multiplier = F::ONE;
        for byte in bytes.iter() {
            value += F::from(*byte as u64) * multiplier;
            multiplier *= F::from(256);
        }
        value
    }
}

/// Returns the random linear combination of the inputs.
/// Encoding is done as follows: v_0 * R^0 + v_1 * R^1 + ...
pub(crate) mod rlc {
    use std::ops::{Add, Mul};

    use crate::util::Expr;
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field, E: Expr<F>>(expressions: &[E], randomness: E) -> Expression<F> {
        if !expressions.is_empty() {
            generic(expressions.iter().map(|e| e.expr()), randomness.expr())
        } else {
            0.expr()
        }
    }

    pub(crate) fn value<'a, F: Field, I>(values: I, randomness: F) -> F
    where
        I: IntoIterator<Item = &'a u8>,
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        let values = values
            .into_iter()
            .map(|v| F::from(*v as u64))
            .collect::<Vec<F>>();
        if !values.is_empty() {
            generic(values, randomness)
        } else {
            F::ZERO
        }
    }

    fn generic<V, I>(values: I, randomness: V) -> V
    where
        I: IntoIterator<Item = V>,
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
        V: Clone + Add<Output = V> + Mul<Output = V>,
    {
        let mut values = values.into_iter().rev();
        let init = values.next().expect("values should not be empty");

        values.fold(init, |acc, value| acc * randomness.clone() + value)
    }
}

/// Returns 2**by as Field
pub(crate) fn pow_of_two<F: Field>(by: usize) -> F {
    F::from(2).pow([by as u64, 0, 0, 0])
}

/// Returns 2**by as Expression
pub(crate) fn pow_of_two_expr<F: Field>(by: usize) -> Expression<F> {
    Expression::Constant(pow_of_two(by))
}

/// Returns tuple consists of low and high part of U256
pub(crate) fn split_u256(value: &U256) -> (U256, U256) {
    (
        U256([value.0[0], value.0[1], 0, 0]),
        U256([value.0[2], value.0[3], 0, 0]),
    )
}

/// Split a U256 value into 4 64-bit limbs stored in U256 values.
pub(crate) fn split_u256_limb64(value: &U256) -> [U256; 4] {
    [
        U256([value.0[0], 0, 0, 0]),
        U256([value.0[1], 0, 0, 0]),
        U256([value.0[2], 0, 0, 0]),
        U256([value.0[3], 0, 0, 0]),
    ]
}

/// Transposes an `Value` of a [`Result`] into a [`Result`] of an `Value`.
pub(crate) fn transpose_val_ret<F, E>(value: Value<Result<F, E>>) -> Result<Value<F>, E> {
    let mut ret = Ok(Value::unknown());
    value.map(|value| {
        ret = value.map(Value::known);
    });
    ret
}

pub(crate) fn is_precompiled(address: &Address) -> bool {
    address.0[0..19] == [0u8; 19] && (1..=9).contains(&address.0[19])
}

const BASE_128_BYTES: [u8; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

/// convert address (h160) to single expression.
pub fn address_word_to_expr<F: Field>(address: Word<Expression<F>>) -> Expression<F> {
    address.lo() + address.hi() * Expression::Constant(F::from_repr(BASE_128_BYTES).unwrap())
}

/// Helper struct to read rw operations from a step sequentially.
pub(crate) struct StepRws<'a> {
    rws: &'a RwMap,
    step: &'a ExecStep,
    offset: usize,
}

impl<'a> StepRws<'a> {
    /// Create a new StateRws by taking the reference to a block and the step.
    pub(crate) fn new<F>(block: &'a Block<F>, step: &'a ExecStep) -> Self {
        Self {
            rws: &block.rws,
            step,
            offset: 0,
        }
    }
    /// Increment the step rw operation offset by `inc`.
    pub(crate) fn offset_add(&mut self, inc: usize) {
        self.offset += inc
    }
    /// Return the next rw operation from the step.
    pub(crate) fn next(&mut self) -> Rw {
        let rw = self.rws[self.step.rw_index(self.offset)];
        self.offset += 1;
        rw
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::evm_circuit::param::STEP_WIDTH;

    use super::*;

    #[test]
    fn test_evm_cm_distribute_advice_1() {
        let mut cs = ConstraintSystem::<Fr>::default();
        let advices = vec![cs.advice_column(); STEP_WIDTH];

        let cm = evm_cm_distribute_advice(&mut cs, &advices);

        let lookup_config_size = LOOKUP_CONFIG
            .iter()
            .map(|(_, size)| size.to_owned())
            .sum::<usize>();

        assert_eq!(
            cm.get(CellType::StoragePhase1).unwrap().len(),
            STEP_WIDTH
                - N_PHASE2_COLUMNS
                - N_COPY_COLUMNS
                - lookup_config_size
                - N_U8_LOOKUPS
                - N_U16_LOOKUPS
        );
        assert_eq!(
            cm.get(CellType::StoragePhase2).unwrap().len(),
            N_PHASE2_COLUMNS
        );
        assert_eq!(
            cm.get(CellType::StoragePermutation).unwrap().len(),
            N_COPY_COLUMNS
        );

        // CellType::Lookup
        for &(table, count) in LOOKUP_CONFIG {
            assert_eq!(cm.get(CellType::Lookup(table)).unwrap().len(), count);
        }
        assert_eq!(
            cm.get(CellType::Lookup(Table::U8)).unwrap().len(),
            N_U8_LOOKUPS
        );
        if N_U16_LOOKUPS == 0 {
            assert!(cm.get(CellType::Lookup(Table::U16)).is_none());
        } else {
            assert_eq!(
                cm.get(CellType::Lookup(Table::U16)).unwrap().len(),
                N_U16_LOOKUPS
            );
        }
    }
}
