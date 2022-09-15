//! Common utility traits and functions.
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Challenge, ConstraintSystem, Expression, FirstPhase},
    poly::Rotation,
};
use std::array;

pub use gadgets::util::Expr;

pub(crate) fn random_linear_combine_word<F: Field>(bytes: [u8; 32], randomness: F) -> F {
    crate::evm_circuit::util::Word::random_linear_combine(bytes, randomness)
}

/// Query N instances at current rotation and return their expressions.  This
/// function is used to get the power of randomness (passed as
/// instances) in our tests.
pub fn power_of_randomness_from_instance<F: Field, const N: usize>(
    meta: &mut ConstraintSystem<F>,
) -> [Expression<F>; N] {
    // This gate is used just to get the array of expressions from the power of
    // randomness instance column, so that later on we don't need to query
    // columns everywhere, and can pass the power of randomness array
    // expression everywhere.  The gate itself doesn't add any constraints.

    let columns = [(); N].map(|_| meta.instance_column());
    let mut power_of_randomness = None;

    meta.create_gate("power of randomness from instance", |meta| {
        power_of_randomness =
            Some(columns.map(|column| meta.query_instance(column, Rotation::cur())));

        [0.expr()]
    });

    power_of_randomness.unwrap()
}

/// All challenges used in `SuperCircuit`.
#[derive(Clone, Copy, Debug)]
pub struct Challenges<T = Challenge> {
    evm_word: T,
    keccak_input: T,
}

impl Challenges {
    /// Construct `Challenges` by allocating challenges in specific phases.
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            evm_word: meta.challenge_usable_after(FirstPhase),
            keccak_input: meta.challenge_usable_after(FirstPhase),
        }
    }

    /// Get `Expression`s from `Layouter` and returns expressions of challenges.
    pub fn exprs<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Challenges<Expression<F>> {
        let mut challenges = array::from_fn(|_| None);
        meta.create_gate("power of randomness from instance", |meta| {
            challenges = [self.evm_word, self.keccak_input]
                .map(|challenge| Some(meta.query_challenge(challenge)));
            Some(0.expr())
        });
        let [evm_word, keccak_input] = challenges.map(Option::unwrap);
        Challenges {
            evm_word,
            keccak_input,
        }
    }

    /// Get `Value`s from `Layouter` and returns values of challenges.
    pub fn values<F: Field>(&self, layouter: &mut impl Layouter<F>) -> Challenges<Value<F>> {
        Challenges {
            evm_word: layouter.get_challenge(self.evm_word),
            keccak_input: layouter.get_challenge(self.keccak_input),
        }
    }
}

impl<T: Clone> Challenges<T> {
    /// Returns challenge of `evm_word`.
    pub fn evm_word(&self) -> T {
        self.evm_word.clone()
    }

    /// Returns challenge of `keccak_input`.
    pub fn keccak_input(&self) -> T {
        self.keccak_input.clone()
    }

    pub(crate) fn mock(challenge: T) -> Self {
        Self {
            evm_word: challenge.clone(),
            keccak_input: challenge,
        }
    }
}
