use halo2::{
    plonk::{Advice, Column, Expression, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;

use crate::param::R_TABLE_LEN;

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

// TODO: use this function in all chips
pub fn compute_rlc<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    advices: Vec<Column<Advice>>,
    mut rind: usize,
    mult: Expression<F>,
    rotation: i32,
    r_table: Vec<Expression<F>>,
) -> Expression<F> {
    let mut r_wrapped = false;
    let mut rlc = Expression::Constant(F::zero());
    for col in advices.iter() {
        let s = meta.query_advice(*col, Rotation(rotation));
        if !r_wrapped {
            rlc = rlc + s * r_table[rind].clone() * mult.clone();
        } else {
            rlc = rlc
                + s * r_table[rind].clone()
                    * r_table[R_TABLE_LEN - 1].clone()
                    * mult.clone();
        }
        if rind == R_TABLE_LEN - 1 {
            rind = 0;
            r_wrapped = true;
        } else {
            rind += 1;
        }
    }

    rlc
}
