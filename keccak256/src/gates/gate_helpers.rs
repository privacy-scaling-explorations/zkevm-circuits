use halo2::circuit::Cell;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;
use std::convert::TryInto;

#[derive(Debug)]
pub struct Lane<F> {
    pub cell: Cell,
    pub value: F,
}

pub fn biguint_to_F<F: FieldExt>(x: BigUint) -> Option<F> {
    Option::from(F::from_bytes(x.to_bytes_le()[..=32].try_into().unwrap()))
}
