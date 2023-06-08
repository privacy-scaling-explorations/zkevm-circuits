use crate::util::word::Word;
use bus_mapping::circuit_input_builder::NumberOrHash;
use eth_types::Field;
use halo2_proofs::circuit::Value;

/// Encode the type `NumberOrHash` into a field element
pub fn number_or_hash_to_field<F: Field>(v: &NumberOrHash) -> Word<Value<F>> {
    match v {
        NumberOrHash::Number(n) => Word::from(*n as u64).into_value(),
        NumberOrHash::Hash(h) => Word::from(*h).into_value(),
    }
}
