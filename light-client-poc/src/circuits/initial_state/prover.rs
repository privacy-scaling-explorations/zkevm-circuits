use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use super::{InitialStateCircuit, circuit::STMHelper };

impl InitialStateCircuit<Fr> {
    pub fn assert_satisfied(&self) {
        let num_rows: usize = self
            .mpt_circuit
            .nodes
            .iter()
            .map(|node| node.values.len())
            .sum();

        let hash = self.lc_witness.initial_values_hash();
        let prover =
            MockProver::<Fr>::run(self.degree as u32, self, vec![vec![hash.lo(), hash.hi()]]).unwrap();
        prover.assert_satisfied_at_rows_par(0..num_rows, 0..num_rows);
    }
}
