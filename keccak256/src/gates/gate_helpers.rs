use halo2::circuit::Cell;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;

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
    let mut word = [0; 32];
    let x_bytes = x.to_bytes_le();
    let len = x_bytes.len();
    assert!(len <= 32);
    word[..len].clone_from_slice(&x_bytes[..len]);
    Option::from(F::from_bytes(&word))
}

pub fn f_to_biguint<F: FieldExt>(x: F) -> Option<BigUint> {
    Option::from(BigUint::from_bytes_le(&x.to_bytes()[..]))
}
