use halo2::circuit::Cell;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;
use std::cmp::min;

#[derive(Debug, Clone)]
pub struct Lane<F> {
    pub cell: Cell,
    pub value: F,
}

#[derive(Debug, Clone, Copy)]
pub struct BlockCount<F> {
    pub cell: Cell,
    pub value: F,
}

pub type BlockCount2<F> = (BlockCount<F>, BlockCount<F>);

pub fn biguint_to_f<F: FieldExt>(x: BigUint) -> Option<F> {
    let mut foo = [0; 32];
    let x_bytes = x.to_bytes_le();
    for idx in 0..min(x_bytes.len(), 32) {
        foo[idx] = x_bytes[idx];
    }
    Option::from(F::from_bytes(&foo))
}

pub fn f_to_biguint<F: FieldExt>(x: F) -> Option<BigUint> {
    Option::from(BigUint::from_bytes_le(&x.to_bytes()[..]))
}
