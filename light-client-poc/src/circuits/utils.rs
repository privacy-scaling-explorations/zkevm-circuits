use eth_types::Field;
use gadgets::util::{and, not};
use halo2_proofs::{plonk::Expression, dev::MockProver, halo2curves::bn256::Fr};

mod equal_words;
mod fixed_rlc;
mod countdown;

pub use equal_words::EqualWordsConfig;
pub use fixed_rlc::FixedRlcConfig;
use zkevm_circuits::mpt_circuit::witness_row::Node;
use eyre::Result;

// negated A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
pub fn xnif<F: Field>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    and::expr([a, not::expr(b)])
}

// A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
pub fn xif<F: Field>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    not::expr(and::expr([a, not::expr(b)]))
}

pub fn verify_mpt_witness(nodes: Vec<Node>) -> Result<()> {
    // get the number of rows in the witness
    let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

    // populate the keccak data
    let mut keccak_data = vec![];
    for node in nodes.iter() {
        for k in node.keccak_data.iter() {
            keccak_data.push(k.to_vec());
        }
    }

    // verify the circuit
    let disable_preimage_check = nodes[0].start.clone().unwrap().disable_preimage_check;
    let degree = 15;
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