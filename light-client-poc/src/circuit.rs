use eyre::Result;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use zkevm_circuits::mpt_circuit::witness_row::Node;

pub fn verify_proof(nodes: Vec<Node>) -> Result<()> {
    // get the number of rows in the witness
    let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

    // populate the keccak data
    let mut keccak_data = vec![];
    for node in nodes.iter() {
        for k in node.keccak_data.iter() {
            keccak_data.push(k.clone());
        }
    }

    // verify the circuit
    let disable_preimage_check = nodes[0].start.clone().unwrap().disable_preimage_check;
    let degree = 14;
    let circuit = zkevm_circuits::mpt_circuit::MPTCircuit::<Fr> {
        nodes,
        keccak_data,
        degree,
        disable_preimage_check,
        _marker: std::marker::PhantomData,
    };

    let prover = MockProver::<Fr>::run(degree as u32, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));

    println!("success!");

    Ok(())
}
