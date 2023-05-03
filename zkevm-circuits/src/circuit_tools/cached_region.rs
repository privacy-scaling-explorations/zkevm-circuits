use crate::{
    circuit_tools::cell_manager::{Cell, CellType_},
    util::Challenges
};
use bus_mapping::state_db::CodeDB;
use eth_types::{Field, ToLittleEndian, ToWord, U256};
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Assigned, Column, Error, Expression, Fixed},
    poly::Rotation,
};
use itertools::Itertools;
use std::{
    hash::{Hash, Hasher},
};

use super::cell_manager::CustomTable;

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
            advice: vec![vec![F::zero(); height]; advice_columns.len()],
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
        // Note that the `value_field` in `AssignedCell` might be `Value::unkonwn` if
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

    pub fn assign_fixed<'v, V, VR, A, AR>(
        &'v mut self,
        annotation: A,
        column: Column<Fixed>,
        offset: usize,
        to: V,
    ) -> Result<AssignedCell<VR, F>, Error>
    where
        V: Fn() -> Value<VR> + 'v,
        for<'vr> Assigned<F>: From<&'vr VR>,
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region.assign_fixed(annotation, column, offset, &to)
    }

    pub fn get_fixed(&self, _row_index: usize, _column_index: usize, _rotation: Rotation) -> F {
        unimplemented!("fixed column");
    }

    pub fn get_advice(&self, row_index: usize, column_index: usize, rotation: Rotation) -> F {
        self.advice[column_index - self.width_start]
            [(((row_index - self.height_start) as i32) + rotation.0) as usize]
    }

    pub fn region(&mut self) -> &mut Region<'_, F> {
        self.region
    }

    pub fn challenges(&self) -> &Challenges<Value<F>> {
        self.challenges
    }

    pub fn word_rlc(&self, n: U256) -> Value<F> {
        self.challenges
            .evm_word()
            .map(|r| rlc::value(&n.to_le_bytes(), r))
    }
    pub fn empty_code_hash_rlc(&self) -> Value<F> {
        self.word_rlc(CodeDB::empty_code_hash().to_word())
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
pub struct StoredExpression<F, T: CustomTable> {
    pub(crate) name: String,
    cell: Cell<F>,
    cell_type: CellType_<T>,
    expr: Expression<F>,
    expr_id: String,
}

impl<F, T: CustomTable> Hash for StoredExpression<F, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expr_id.hash(state);
        self.cell_type.hash(state);
    }
}

impl<F: Field, T: CustomTable> StoredExpression<F, T>  {
    pub fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
    ) -> Result<Value<F>, Error> {
        let value = self.expr.evaluate(
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
        );
        self.cell.assign_value(region, offset, value)?;
        Ok(value)
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
            F::zero()
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