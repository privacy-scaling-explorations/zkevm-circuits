//! This module contains a collection of utility functions that help to
//! construct expressions to be used inside gate constraints.

use digest::generic_array::typenum::Exp;
use eth_types::Field;
use halo2_proofs::plonk::Expression;

/// This function generates a Lagrange polynomial in the range [start, end)
/// which will be evaluated to 1 when `exp == value`, otherwise 0
pub fn generate_lagrange_base_polynomial<F: Field, R: Iterator<Item = usize>>(
    exp: Expression<F>,
    val: usize,
    range: R,
) -> Expression<F> {
    let mut numerator = Expression::Constant(F::one());
    let mut denominator = F::one();
    for x in range {
        if x != val {
            numerator = numerator * (exp.clone() - Expression::Constant(F::from(x as u64)));
            denominator *= F::from(val as u64) - F::from(x as u64);
        }
    }
    numerator * denominator.invert().unwrap()
}

/// Generate an expression which constraints an expression to be boolean.
/// Returns 0 if it is.
/// Based on: `(1-expr) * expr = 0` only if `expr` is boolean.
pub fn bool_constraint_expr<F: Field>(exp: Expression<F>) -> Expression<F> {
    (Expression::Constant(F::one()) - exp.clone()) * exp
}

/// Generates an expression which equals 0 if the expr is within the range
/// provided by the user. It does so by: `(range[0] - expr) * ... * (range[N-1]
/// - expr)`.
pub fn is_within_range<F: Field, R: Iterator<Item = usize>>(
    expr: Expression<F>,
    range: R,
) -> Expression<F> {
    range
        .into_iter()
        .fold(Expression::Constant(F::one()), |acc, x| {
            acc * (Expression::Constant(F::from(x as u64)) - expr.clone())
        })
}

/// Performs `base.pow(exp)` with log(N) complexity by squaring the base and
/// multiplying the coefficients until the exp is achieved.
pub fn square_and_multiply<F: Field>(base: Expression<F>, exp: usize) -> Expression<F> {
    let mut powers = vec![];
    let mut acc = base.clone();
    let mut exp_acc = 2usize;
    let final_exp = if exp.is_power_of_two() {
        exp
    } else {
        exp.next_power_of_two()
    };
    // Fill the buckets with [base, base^2, base^4.... base^(log2(exp))]
    while exp_acc <= final_exp {
        acc = acc.clone() * base.clone();
        powers.push((acc.clone(), exp));
        exp_acc *= 2;
    }

    // If the exp was a power of two, we can return the last expr computed.
    if exp.is_power_of_two() {
        return powers.last().unwrap().0.clone();
    }

    let mut remainder = exp - powers.last().unwrap().1;
    for (base_power, exp) in powers.iter().rev() {
        if *exp <= remainder {
            remainder = remainder - exp;
            acc = acc * base_power.clone();
        }
    }

    acc
}

/// Utilities to generate expressions related to Random Linear Combination
/// procedures.
pub mod rlc {
    use super::*;

    /// Generate an Expression which computes the RLC for the given expressions
    /// and randomness.
    /// It also computes the powers of the randomness needed to compute the RLC
    /// for the entire expr set.
    pub fn compose<F: Field, const N: usize>(
        expressions: &[Expression<F>],
        mut randomness: Expression<F>,
    ) -> Expression<F> {
        let og_rand = randomness.clone();
        let mut rlc = expressions[0].clone();
        for expression in expressions[1..].iter() {
            rlc = rlc + expression.clone() * randomness.clone();
            randomness = randomness * og_rand.clone();
        }
        rlc
    }

    /// Generate an Expression which computes the RLC for the given expressions
    /// and randomness.
    pub fn compose_with_powers<F: Field, const N: usize>(
        expressions: &[Expression<F>],
        powers_of_randomness: &[Expression<F>],
    ) -> Expression<F> {
        debug_assert!(expressions.len() <= powers_of_randomness.len() + 1);

        let mut rlc = expressions[0].clone();
        for (expression, randomness) in expressions[1..].iter().zip(powers_of_randomness.iter()) {
            rlc = rlc + expression.clone() * randomness.clone();
        }
        rlc
    }
}
