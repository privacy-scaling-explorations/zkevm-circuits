//! This module contains a collection of utility functions that help to
//! construct expressions to be used inside gate constraints.

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
