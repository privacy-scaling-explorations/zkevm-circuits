//! Common utility traits and functions.
pub mod int_decomposition;
pub mod word;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{
        Advice, Assigned, Challenge, Column, ConstraintSystem, Error, Expression, FirstPhase,
        SecondPhase, VirtualCells,
    },
    poly::Rotation,
};
use itertools::Itertools;

#[cfg(not(feature = "js"))]
use crate::{table::TxLogFieldTag};

use crate::{witness};
use eth_types::{keccak256, Field, ToAddress, Word};
pub use ethers_core::types::{Address, U256};
pub use gadgets::util::Expr;

/// Cell Manager
pub mod cell_manager;
/// Cell Placement strategies
pub mod cell_placement_strategy;

use std::hash::{Hash, Hasher};

/// Steal the expression from gate
pub fn query_expression<F: Field, T>(
    meta: &mut ConstraintSystem<F>,
    mut f: impl FnMut(&mut VirtualCells<F>) -> T,
) -> T {
    let mut expr = None;
    meta.create_gate("Query expression", |meta| {
        expr = Some(f(meta));
        Some(0.expr())
    });
    expr.unwrap()
}

/// All challenges used in `SuperCircuit`.
#[derive(Default, Clone, Copy, Debug)]
pub struct Challenges<T = Challenge> {
    keccak_input: T,
    lookup_input: T,
}

impl Challenges {
    /// Construct `Challenges` by allocating challenges in specific phases.
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        // Dummy columns are required in the test circuits
        // In some tests there might be no advice columns before the phase, so Halo2 will panic with
        // "No Column<Advice> is used in phase Phase(1) while allocating a new 'Challenge usable
        // after phase Phase(1)'"
        #[cfg(any(test, feature = "test-circuits"))]
        let _dummy_cols = [meta.advice_column(), meta.advice_column_in(SecondPhase)];

        Self {
            keccak_input: meta.challenge_usable_after(FirstPhase),
            lookup_input: meta.challenge_usable_after(SecondPhase),
        }
    }

    /// Returns `Expression` of challenges from `ConstraintSystem`.
    pub fn exprs<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Challenges<Expression<F>> {
        let [keccak_input, lookup_input] = query_expression(meta, |meta| {
            [self.keccak_input, self.lookup_input].map(|challenge| meta.query_challenge(challenge))
        });
        Challenges {
            keccak_input,
            lookup_input,
        }
    }

    /// Returns `Value` of challenges from `Layouter`.
    pub fn values<F: Field>(&self, layouter: &mut impl Layouter<F>) -> Challenges<Value<F>> {
        Challenges {
            keccak_input: layouter.get_challenge(self.keccak_input),
            lookup_input: layouter.get_challenge(self.lookup_input),
        }
    }
}

impl<T: Clone> Challenges<T> {
    /// Returns challenge of `keccak_input`.
    pub fn keccak_input(&self) -> T {
        self.keccak_input.clone()
    }

    /// Returns challenge of `lookup_input`.
    pub fn lookup_input(&self) -> T {
        self.lookup_input.clone()
    }

    /// Returns the challenges indexed by the challenge index
    pub fn indexed(&self) -> [&T; 2] {
        [&self.keccak_input, &self.lookup_input]
    }

    /// Mocks challange values for testing
    pub fn mock(keccak_input: T, lookup_input: T) -> Self {
        Self {
            keccak_input,
            lookup_input,
        }
    }
}

impl<F: Field> Challenges<Expression<F>> {
    /// Returns powers of randomness
    fn powers_of<const S: usize>(base: Expression<F>) -> [Expression<F>; S] {
        std::iter::successors(base.clone().into(), |power| {
            (base.clone() * power.clone()).into()
        })
        .take(S)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
    }

    /// Returns powers of randomness for keccak circuit's input
    pub fn keccak_powers_of_randomness<const S: usize>(&self) -> [Expression<F>; S] {
        Self::powers_of(self.keccak_input.clone())
    }

    /// Returns powers of randomness for lookups
    pub fn lookup_input_powers_of_randomness<const S: usize>(&self) -> [Expression<F>; S] {
        Self::powers_of(self.lookup_input.clone())
    }
}

#[cfg(not(feature = "js"))]
pub(crate) fn build_tx_log_address(index: u64, field_tag: TxLogFieldTag, log_id: u64) -> Address {
    (U256::from(index) + (U256::from(field_tag as u64) << 32) + (U256::from(log_id) << 48))
        .to_address()
}

pub(crate) fn build_tx_log_expression<F: Field>(
    index: Expression<F>,
    field_tag: Expression<F>,
    log_id: Expression<F>,
) -> Expression<F> {
    index + (1u64 << 32).expr() * field_tag + ((1u64 << 48).expr()) * log_id
}

/// SubCircuit is a circuit that performs the verification of a specific part of
/// the full Ethereum block verification.  The SubCircuit's interact with each
/// other via lookup tables and/or shared public inputs.  This type must contain
/// all the inputs required to synthesize this circuit (and the contained
/// table(s) if any).
pub trait SubCircuit<F: Field> {
    /// Configuration of the SubCircuit.
    type Config: SubCircuitConfig<F>;

    /// Returns number of unusable rows of the SubCircuit, which should be
    /// `meta.blinding_factors() + 1`.
    fn unusable_rows() -> usize;

    /// Create a new SubCircuit from a witness Block
    #[cfg(not(feature = "js"))]
    fn new_from_block(block: &witness::Block<F>) -> Self;

    /// Returns the instance columns required for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        vec![]
    }
    /// Assign only the columns used by this sub-circuit.  This includes the
    /// columns that belong to the exposed lookup table contained within, if
    /// any; and excludes external tables that this sub-circuit does lookups
    /// to.
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error>;

    /// Return the minimum number of rows required to prove the block.
    /// Row numbers without/with padding are both returned.
    #[cfg(not(feature = "js"))]
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize);
}

/// SubCircuit configuration
pub trait SubCircuitConfig<F: Field> {
    /// Config constructor arguments
    type ConfigArgs;

    /// Type constructor
    fn new(meta: &mut ConstraintSystem<F>, args: Self::ConfigArgs) -> Self;
}

/// Ceiling of log_2(n)
pub fn log2_ceil(n: usize) -> u32 {
    u32::BITS - (n as u32).leading_zeros() - (n & (n - 1) == 0) as u32
}

pub(crate) fn keccak(msg: &[u8]) -> Word {
    Word::from_big_endian(keccak256(msg).as_slice())
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

/// Decodes a field element from its byte representation in little endian order
pub(crate) mod from_bytes {
    use crate::util::Expr;
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    const MAX_N_BYTES_INTEGER: usize = 31;

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

///
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


    pub(crate) fn get_fixed(&self, _row_index: usize, _column_index: usize, _rotation: Rotation) -> F {
        unimplemented!("fixed column");
    }

    pub(crate) fn get_advice(&self, row_index: usize, column_index: usize, rotation: Rotation) -> F {
        self.advice[column_index - self.width_start]
            [(((row_index - self.height_start) as i32) + rotation.0) as usize]
    }

    pub(crate) fn challenges(&self) -> &Challenges<Value<F>> {
        self.challenges
    }

    pub(crate) fn keccak_rlc(&self, le_bytes: &[u8]) -> Value<F> {
        self.challenges
            .keccak_input()
            .map(|r| rlc::value(le_bytes, r))
    }

    pub(crate) fn code_hash(&self, n: U256) -> word::Word<Value<F>> {
        word::Word::from(n).into_value()
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
pub(crate) struct StoredExpression<F> {
    pub(crate) name: String,
    pub(crate) cell: Cell<F>,
    pub(crate) cell_type: CellType,
    pub(crate) expr: Expression<F>,
    pub(crate) expr_id: String,
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

#[cfg(test)]
use halo2_proofs::plonk::Circuit;

use self::cell_manager::{Cell, CellType};

#[cfg(test)]
/// Returns number of unusable rows of the Circuit.
/// The minimum unusable rows of a circuit is currently 6, where
/// - 3 comes from minimum number of distinct queries to permutation argument witness column
/// - 1 comes from queries at x_3 during multiopen
/// - 1 comes as slight defense against off-by-one errors
/// - 1 comes from reservation for last row for grand-product boundray check, hence not copy-able or
///   lookup-able. Note this 1 is not considered in [`ConstraintSystem::blinding_factors`], so below
///   we need to add an extra 1.
///
/// For circuit with column queried at more than 3 distinct rotation, we can
/// calculate the unusable rows as (x - 3) + 6 where x is the number of distinct
/// rotation.
pub(crate) fn unusable_rows<F: Field, C: Circuit<F>>(params: C::Params) -> usize {
    let mut cs = ConstraintSystem::default();
    C::configure_with_params(&mut cs, params);

    cs.blinding_factors() + 1
}
