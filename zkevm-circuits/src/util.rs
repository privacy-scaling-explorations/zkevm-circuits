//! Common utility traits and functions.
pub mod int_decomposition;
pub mod word;

use bus_mapping::evm::OpcodeId;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        Challenge, ConstraintSystem, Error, Expression, FirstPhase, SecondPhase, VirtualCells,
    },
};

use crate::{
    table::TxLogFieldTag,
    witness::{self, Chunk},
};
use eth_types::{keccak256, Field, ToAddress, Word};
pub use ethers_core::types::{Address, U256};
pub use gadgets::util::Expr;

/// Cell Manager
pub mod cell_manager;
/// Cell Placement strategies
pub mod cell_placement_strategy;

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

    pub(crate) fn mock(keccak_input: T, lookup_input: T) -> Self {
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
    fn new_from_block(block: &witness::Block<F>, chunk: Option<&Chunk<F>>) -> Self;

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

pub(crate) fn is_push_with_data(byte: u8) -> bool {
    OpcodeId::from(byte).is_push_with_data()
}

pub(crate) fn get_push_size(byte: u8) -> u64 {
    if is_push_with_data(byte) {
        byte as u64 - OpcodeId::PUSH0.as_u64()
    } else {
        0u64
    }
}

pub(crate) fn unwrap_value<T>(value: Value<T>) -> T {
    let mut inner = None;
    _ = value.map(|v| {
        inner = Some(v);
    });
    inner.unwrap()
}

#[cfg(test)]
use halo2_proofs::plonk::Circuit;

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
