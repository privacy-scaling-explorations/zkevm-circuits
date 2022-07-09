//! Common utility traits and functions.
use bus_mapping::operation::Target;
use eth_types::{
    evm_types::{GasCost, OpcodeId},
    Field,
};
use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

/// Keccak256 hash of empty input in big-endian
pub const EMPTY_HASH: [u8; 32] = [
    0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70,
];
/// Keccak256 hash of empty input in little-endian
pub const EMPTY_HASH_LE: [u8; 32] = [
    0x70, 0xa4, 0x85, 0x5d, 0x04, 0xd8, 0xfa, 0x7b, 0x3b, 0x27, 0x82, 0xca, 0x53, 0xb6, 0x00, 0xe5,
    0xc0, 0x03, 0xc7, 0xdc, 0xb2, 0x7d, 0x7e, 0x92, 0x3c, 0x23, 0xf7, 0x86, 0x01, 0x46, 0xd2, 0xc5,
];

pub(crate) trait Expr<F: FieldExt> {
    fn expr(&self) -> Expression<F>;
}

/// Implementation trait `Expr` for type able to be casted to u64
#[macro_export]
macro_rules! impl_expr {
    ($type:ty) => {
        impl<F: FieldExt> $crate::util::Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from(*self as u64))
            }
        }
    };
    ($type:ty, $method:path) => {
        impl<F: FieldExt> Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from($method(self) as u64))
            }
        }
    };
}

impl_expr!(bool);
impl_expr!(u8);
impl_expr!(u64);
impl_expr!(usize);
impl_expr!(Target);
impl_expr!(OpcodeId, OpcodeId::as_u8);
impl_expr!(GasCost, GasCost::as_u64);

impl<F: FieldExt> Expr<F> for Expression<F> {
    #[inline]
    fn expr(&self) -> Expression<F> {
        self.clone()
    }
}

impl<F: FieldExt> Expr<F> for &Expression<F> {
    #[inline]
    fn expr(&self) -> Expression<F> {
        (*self).clone()
    }
}

impl<F: FieldExt> Expr<F> for i32 {
    #[inline]
    fn expr(&self) -> Expression<F> {
        Expression::Constant(
            F::from(self.abs() as u64)
                * if self.is_negative() {
                    -F::one()
                } else {
                    F::one()
                },
        )
    }
}

pub(crate) fn random_linear_combine_word<F: Field>(bytes: [u8; 32], randomness: F) -> F {
    crate::evm_circuit::util::Word::random_linear_combine(bytes, randomness)
}
