//! Common utility traits and functions.
use bus_mapping::{
    evm::{GasCost, OpcodeId},
    operation::Target,
};
use halo2::{arithmetic::FieldExt, plonk::Expression};
use num::BigUint;

pub(crate) trait Expr<F: FieldExt> {
    fn expr(&self) -> Expression<F>;
}

macro_rules! impl_unsigned_expr {
    ($type:ty) => {
        impl<F: FieldExt> Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from_u64(*self as u64))
            }
        }
    };
    ($type:ty, $method:path) => {
        impl<F: FieldExt> Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from_u64($method(self) as u64))
            }
        }
    };
}

macro_rules! impl_signed_expr {
    ($type:ty) => {
        impl<F: FieldExt> Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(
                    F::from_u64(self.abs() as u64)
                        * if self.is_negative() {
                            -F::one()
                        } else {
                            F::one()
                        },
                )
            }
        }
    };
}

impl_unsigned_expr!(bool);
impl_unsigned_expr!(u8);
impl_unsigned_expr!(u64);
impl_unsigned_expr!(usize);
impl_unsigned_expr!(Target);
impl_unsigned_expr!(OpcodeId, OpcodeId::as_u8);
impl_unsigned_expr!(GasCost, GasCost::as_u64);

impl_signed_expr!(i32);

pub(crate) trait ToWord {
    /// Convert the value into 32 8-bit bytes in little endian
    fn to_word(&self) -> [u8; 32];
}

impl ToWord for BigUint {
    #[inline]
    fn to_word(&self) -> [u8; 32] {
        let mut ret = [0u8; 32];
        for (pos, v) in self.to_bytes_le().iter().enumerate() {
            ret[pos] = *v
        }
        ret
    }
}
