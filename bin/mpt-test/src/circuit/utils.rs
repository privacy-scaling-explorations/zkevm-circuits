//! Some utilities.

use crate::circuit::witness::FieldTrieModifications;
use eth_types::Field;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use std::ops::Deref;

use super::state_update::StateUpdateCircuit;

pub struct PublicInputs<F: Field>(pub Vec<F>);
impl<F: Field> Deref for PublicInputs<F> {
    type Target = Vec<F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Field> From<&FieldTrieModifications<F>> for PublicInputs<F> {
    fn from(stm: &FieldTrieModifications<F>) -> Self {
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

impl StateUpdateCircuit<Fr> {
    pub fn assert_satisfied(&self) {
        let num_rows: usize = self
            .mpt_circuit
            .nodes
            .iter()
            .map(|node| node.values.len())
            .sum();

        let public_inputs: PublicInputs<Fr> = (&self.lc_witness).into();

        let prover =
            MockProver::<Fr>::run(self.degree as u32, self, vec![public_inputs.0]).unwrap();

        prover.assert_satisfied_at_rows(0..num_rows, 0..num_rows);
    }
}
