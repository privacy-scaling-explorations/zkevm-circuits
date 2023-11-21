use eth_types::Field;
use gadgets::util::{and, not};
use halo2_proofs::plonk::Expression;

mod equal_words;
mod fixed_rlc;
mod countdown;

pub use equal_words::EqualWordsConfig;
pub use fixed_rlc::FixedRlcConfig;

// negated A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
pub fn xnif<F: Field>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    and::expr([a, not::expr(b)])
}

// A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
pub fn xif<F: Field>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    not::expr(and::expr([a, not::expr(b)]))
}