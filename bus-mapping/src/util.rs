//! Common utility traits and functions.

use num::BigUint;
use pasta_curves::arithmetic::FieldExt;

/// Serializes a field element
pub fn serialize_field_ext<S, F>(
    v: &F,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
    F: FieldExt,
{
    serializer
        .serialize_str(&BigUint::from_bytes_le(&v.to_bytes()).to_str_radix(16))
}
