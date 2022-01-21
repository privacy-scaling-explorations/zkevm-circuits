use halo2::plonk::Expression;
use pairing::arithmetic::FieldExt;

// Turn 32 hash cells into 4 cells containing keccak words.
pub fn into_words_expr<F: FieldExt>(
    hash: Vec<Expression<F>>,
) -> Vec<Expression<F>> {
    let mut words = vec![];
    for i in 0..4 {
        let mut word = Expression::Constant(F::zero());
        let mut exp = Expression::Constant(F::one());
        for j in 0..8 {
            word = word + hash[i * 8 + j].clone() * exp.clone();
            exp = exp * Expression::Constant(F::from(256));
        }
        words.push(word)
    }

    words
}
