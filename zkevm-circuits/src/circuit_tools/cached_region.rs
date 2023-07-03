use crate::circuit_tools::cell_manager::Cell;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Any, Assigned, Column, Error, Expression, Fixed},
    poly::Rotation,
};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

use super::{cell_manager::CellType, constraint_builder::ConstraintBuilder};

pub trait ChallengeSet<F: Field> {
    fn indexed(&self) -> Vec<&Value<F>>;
}

impl<F: Field, V: AsRef<[Value<F>]>> ChallengeSet<F> for V {
    fn indexed(&self) -> Vec<&Value<F>> {
        self.as_ref().iter().collect()
    }
}

pub struct CachedRegion<'r, 'b, F: Field> {
    region: &'r mut Region<'b, F>,
    pub advice: HashMap<(usize, usize), F>,
    pub fixed: HashMap<(usize, usize), F>,
    disable_description: bool,
    regions: Vec<(usize, usize)>,
    pub r: F,
    pub keccak_r: F,
}

impl<'r, 'b, F: Field> CachedRegion<'r, 'b, F> {
    pub(crate) fn new(region: &'r mut Region<'b, F>, r: F, keccak_r: F) -> Self {
        Self {
            region,
            advice: HashMap::new(),
            fixed: HashMap::new(),
            disable_description: false,
            regions: Vec::new(),
            r,
            keccak_r,
        }
    }

    pub(crate) fn set_disable_description(&mut self, disable_description: bool) {
        self.disable_description = disable_description;
    }

    pub(crate) fn push_region(&mut self, offset: usize, region_id: usize) {
        self.regions.push((offset, region_id));
    }

    pub(crate) fn pop_region(&mut self) {
        // Nothing to do
    }

    pub(crate) fn assign_stored_expressions<C: CellType, S: ChallengeSet<F>>(
        &mut self,
        cb: &ConstraintBuilder<F, C>,
        challenges: &S,
    ) -> Result<(), Error> {
        for (offset, region_id) in self.regions.clone() {
            for stored_expression in cb.get_stored_expressions(region_id).iter() {
                //println!("stored expression: {}", stored_expression.name);
                stored_expression.assign(self, challenges, offset)?;
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
            to().map(|f: VR| {
                let existing = self
                    .advice
                    .insert((column.index(), offset), Assigned::from(&f).evaluate());
                assert!(existing.is_none());
                existing
            });
        }
        res
    }

    pub fn name_column<A, AR, T>(&mut self, annotation: A, column: T)
    where
        A: Fn() -> AR,
        AR: Into<String>,
        T: Into<Column<Any>>,
    {
        self.region
            .name_column(|| annotation().into(), column.into());
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
        // Actually set the value
        let res = self.region.assign_fixed(annotation, column, offset, &to);
        // Cache the value
        // Note that the `value_field` in `AssignedCell` might be `Value::unkonwn` if
        // the column has different phase than current one, so we call to `to`
        // again here to cache the value.
        if res.is_ok() {
            to().map(|f: VR| {
                let existing = self
                    .fixed
                    .insert((column.index(), offset), Assigned::from(&f).evaluate());
                assert!(existing.is_none());
                existing
            });
        }
        res
    }

    pub fn get_fixed(&self, row_index: usize, column_index: usize, rotation: Rotation) -> F {
        let zero = F::ZERO;
        *self
            .fixed
            .get(&(column_index, row_index + rotation.0 as usize))
            .unwrap_or(&zero)
    }

    pub fn get_advice(&self, row_index: usize, column_index: usize, rotation: Rotation) -> F {
        let zero = F::ZERO;
        *self
            .advice
            .get(&(column_index, row_index + rotation.0 as usize))
            .unwrap_or(&zero)
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
pub struct StoredExpression<F, C: CellType> {
    pub(crate) name: String,
    pub(crate) cell: Cell<F>,
    pub(crate) cell_type: C,
    pub(crate) expr: Expression<F>,
    pub(crate) expr_id: String,
}

impl<F, C: CellType> Hash for StoredExpression<F, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expr_id.hash(state);
        self.cell_type.hash(state);
    }
}

impl<F: Field, C: CellType> StoredExpression<F, C> {
    pub fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        challenges: &S,
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
            &|challenge| *challenges.indexed()[challenge.index()],
            &|a| -a,
            &|a, b| a + b,
            &|a, b| a * b,
            &|a, scalar| a * Value::known(scalar),
        );
        self.cell.assign_value(region, offset, value)?;
        Ok(value)
    }
}
