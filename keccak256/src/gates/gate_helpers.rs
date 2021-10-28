use halo2::circuit::Cell;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;
use std::convert::TryInto;

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
    Option::from(F::from_bytes(x.to_bytes_le()[..=32].try_into().unwrap()))
}

pub fn f_to_biguint<F: FieldExt>(x: F) -> Option<BigUint> {
    Option::from(BigUint::from_bytes_le(&x.to_bytes()[..]))
}
