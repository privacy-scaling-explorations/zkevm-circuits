use halo2::{circuit::Cell, plonk::Error};
use num_bigint::BigUint;
use pairing::arithmetic::FieldExt;

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

pub fn biguint_to_f<F: FieldExt>(x: &BigUint) -> Result<F, Error> {
    let mut word = [0; 32];
    let x_bytes = x.to_bytes_le();
    let len = x_bytes.len();
    assert!(len <= 32, "expect len <=32 but got {}", len);
    word[..len].clone_from_slice(&x_bytes[..len]);
    Option::from(F::from_bytes(&word)).ok_or(Error::Synthesis)
}

pub fn f_to_biguint<F: FieldExt>(x: F) -> Option<BigUint> {
    Option::from(BigUint::from_bytes_le(&x.to_bytes()[..]))
}

pub fn biguint_mod(x: &BigUint, modulus: u8) -> u8 {
    x.to_radix_le(modulus.into())
        .first()
        .copied()
        .unwrap_or_default()
}
