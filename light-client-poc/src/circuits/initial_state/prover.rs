use halo2_proofs::{halo2curves::bn256::Fr, dev::MockProver};

use super::{InitialStateCircuit, pi::PublicInputs};

impl InitialStateCircuit<Fr> {
    pub fn assert_satisfied(&self) {
        let num_rows: usize = self
            .mpt_circuit
            .nodes
            .iter()
            .map(|node| node.values.len())
            .sum();

        let public_inputs: PublicInputs<Fr> = (&self.lc_witness).into();

        for (i, input) in public_inputs.iter().enumerate() {
            println!("input[{i:}]: {input:?}");
        }

        let prover =
            MockProver::<Fr>::run(self.degree as u32, self, vec![public_inputs.0]).unwrap();
        prover.assert_satisfied_at_rows_par(0..num_rows, 0..num_rows);
    }
}