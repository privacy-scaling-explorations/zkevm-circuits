use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

use super::{pi::PublicInputs, InitialStateCircuit};

impl InitialStateCircuit<Fr> {
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
        prover.assert_satisfied_at_rows_par(0..num_rows, 0..num_rows);
    }
}
