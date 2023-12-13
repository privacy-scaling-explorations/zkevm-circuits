use crate::witness::SingleTrieModifications;
use eth_types::Field;
use std::ops::Deref;

pub struct PublicInputs<F: Field>(pub Vec<F>);
impl<F: Field> Deref for PublicInputs<F> {
    type Target = Vec<F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Field> From<&SingleTrieModifications<F>> for PublicInputs<F> {
    fn from(stm: &SingleTrieModifications<F>) -> Self {
        let mut inputs = vec![
            stm.0[0].old_root.lo(),
            stm.0[0].old_root.hi(),
            stm.0.last().unwrap().new_root.lo(),
            stm.0.last().unwrap().new_root.hi(),
            F::from(stm.0.len() as u64),
        ];

        for proof in &stm.0 {
            inputs.push(proof.typ);
            inputs.push(proof.address);
            inputs.push(proof.value.lo());
            inputs.push(proof.value.hi());
            inputs.push(proof.key.lo());
            inputs.push(proof.key.hi());
        }

        PublicInputs(inputs)
    }
}
