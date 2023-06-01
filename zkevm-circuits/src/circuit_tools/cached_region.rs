use crate::{
    circuit_tools::cell_manager::{Cell, EvmCellType},
};
use eth_types::{Field};
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Assigned, Column, Error, Expression, Fixed, Any},
    poly::Rotation,
};
use itertools::Itertools;
use std::{
    hash::{Hash, Hasher}, collections::HashMap,
};

use super::cell_manager::CellTypeTrait;

pub trait ChallengeSet<F: Field> {
    fn indexed(&self) -> Vec<&Value<F>>;
}

impl<F: Field, V: AsRef<[Value<F>]>> ChallengeSet<F> for V {
    fn indexed(&self) -> Vec<&Value<F>> {
        self.as_ref().iter().collect()
    }
}

pub trait MacroDescr {
    fn is_descr_disabled(&self) -> bool;
}

impl<'r, F: Field> MacroDescr for Region<'r, F> {
    fn is_descr_disabled(&self) -> bool {
        false
    }
}


pub struct CachedRegion<'r, 'b, F: Field, S: ChallengeSet<F>> {
    region: &'r mut Region<'b, F>,
    pub advice: HashMap<(usize, usize), F>,
    challenges: &'r S,
    disable_description: bool,
}

impl<'r, 'b, F: Field, S: ChallengeSet<F>> CachedRegion<'r, 'b, F, S> {
    pub(crate) fn new(
        region: &'r mut Region<'b, F>,
        challenges: &'r S,
    ) -> Self {
        Self {
            region,
            advice: HashMap::new(),
            challenges,
            disable_description: false,
        }
    }

    pub(crate) fn disable_description(&mut self) {
        self.disable_description = true;
    }

    pub(crate) fn is_descr_disabled(&self) -> bool {
        self.disable_description
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
                self.advice.insert((column.index(), offset),  Assigned::from(&f).evaluate());
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
            .name_column(&|| annotation().into(), column.into());
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

    // StoreExpression 里面调，拿 F 出去 evaluate
    pub fn get_advice(&self, row_index: usize, column_index: usize, rotation: Rotation) -> F {
        println!("\t get_advice: [{}][{}]", column_index, rotation.0 as usize + row_index);
        self.advice.get(&(column_index, row_index + rotation.0 as usize))
            .expect("Advice not found")
            .clone()
    }

    pub fn challenges(&self) -> &S {
        self.challenges
    }


    // pub fn word_rlc(&self, n: U256) -> Value<F> {
    //     self.challenges
    //         .evm_word()
    //         .map(|r| rlc::value(&n.to_le_bytes(), r))
    // }
    // pub fn empty_code_hash_rlc(&self) -> Value<F> {
    //     self.word_rlc(CodeDB::empty_code_hash().to_word())
    // }


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
pub struct StoredExpression<F, C: CellTypeTrait> {
    pub(crate) name: String,
    pub(crate) cell: Cell<F>,
    pub(crate) cell_type: C,
    pub(crate) expr: Expression<F>,
    pub(crate) expr_id: String,
}

impl<F, C: CellTypeTrait> Hash for StoredExpression<F, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expr_id.hash(state);
        self.cell_type.hash(state);
    }
}

impl<F: Field, C: CellTypeTrait> StoredExpression<F, C>  {
    pub fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
    ) -> Result<Value<F>, Error> {

        //println!("____ StoredExpression::assign ____ \n\t {:?} -> {:?}", self.expr_id, self.cell.identifier());
        
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
        println!("evaluated value: {:?}", value);
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