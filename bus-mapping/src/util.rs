//! Common utility traits and functions.

use crate::operation::EvmWord;
use pasta_curves::arithmetic::FieldExt;
use serde::Serialize;

/// Serializes a field element
pub fn serialize_field_ext<S, F>(
    v: &F,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
    F: FieldExt,
{
    EvmWord::from_le_bytes(&v.to_bytes())
        .unwrap()
        .serialize(serializer)
}
