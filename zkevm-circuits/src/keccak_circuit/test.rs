use super::*;
use crate::evm_circuit::util::rlc;
use halo2_proofs::dev::{unwrap_value, CellValue, MockProver};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::Assignment;
use itertools::izip;
use log::error;

const EMPTY_DIGEST: &str = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470";

fn verify<F: Field>(k: u32, inputs: Vec<Vec<u8>>, digests: Vec<String>, success: bool) {
    let circuit = KeccakCircuit::new(2usize.pow(k), inputs.clone());
    let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
    let (config, challenges) = KeccakCircuit::configure(&mut ConstraintSystem::<F>::default());
    let input_challenge = unwrap_value(prover.get_challenge(challenges.keccak_input()));
    let hash_challenge = unwrap_value(prover.get_challenge(challenges.evm_word()));

    // Check constraints.
    let verify_result = prover.verify();
    if verify_result.is_ok() != success {
        if let Some(errors) = verify_result.err() {
            for error in errors.iter() {
                error!("{}", error);
            }
        }
        panic!();
    }

    // Extract the content of the lookup table.
    let hash_lookup_table = {
        // Find the columns of the table.
        let is_enabled = prover.advice_values(config.keccak_table.is_enabled);
        let input_rlc = prover.advice_values(config.keccak_table.input_rlc);
        let input_len = prover.advice_values(config.keccak_table.input_len);
        let output_rlc = prover.advice_values(config.keccak_table.output_rlc);

        // Keep the rows that are supposed to contain hash results.
        izip!(is_enabled, input_rlc, input_len, output_rlc)
            .filter(|(enabled, _, _, _)| assigned_non_zero(enabled))
            .map(|(_, input_rlc, input_len, output_rlc)| {
                (unwrap(input_rlc), unwrap(input_len), unwrap(output_rlc))
            })
            .collect::<Vec<(F, F, F)>>()
    };

    // Calculate the expected inputs in reversed-RLC form.
    let rlc_input = |bytes: &[u8]| rlc::value(bytes.iter().rev(), input_challenge);

    // Calculate the expected digests in reversed-RLC form.
    let rlc_digest = |hex_str: &str| {
        let bytes = hex::decode(hex_str).unwrap();
        rlc::value(bytes.iter().rev(), hash_challenge)
    };

    // Check that all the digests are there.
    assert!(hash_lookup_table.len() >= inputs.len());
    assert_eq!(inputs.len(), digests.len());
    for (input, digest, hash) in izip!(&inputs, &digests, &hash_lookup_table) {
        let len = F::from(input.len() as u64);
        let expected = (rlc_input(input), len, rlc_digest(digest));
        assert_eq!(*hash, expected);
    }

    // Check that other digests are the digest of the empty message.
    let empty_hash = (F::zero(), F::zero(), rlc_digest(EMPTY_DIGEST));
    for hash in hash_lookup_table.iter().skip(inputs.len()) {
        assert_eq!(*hash, empty_hash);
    }
}

#[test]
fn packed_multi_keccak_simple() {
    let k = 14;
    let inputs = vec![
        vec![],
        vec![0],
        (0u8..135).collect::<Vec<_>>(),
        (0u8..136).collect::<Vec<_>>(),
        (0u8..137).collect::<Vec<_>>(),
        (0..400).map(|i| (1 + 3 * i) as u8).collect::<Vec<_>>(),
    ];
    let digests = vec![
        EMPTY_DIGEST.to_string(),
        "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a".to_string(),
        "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62".to_string(),
        "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e".to_string(),
        "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db".to_string(),
        "f46dfb05481d2a50c0c3b6625d913055da3e07dcd0d6c661f27f1449b0fed7eb".to_string(),
    ];
    verify::<Fr>(k, inputs, digests, true);
}

fn assigned_non_zero<F: Field>(cv: &CellValue<F>) -> bool {
    match *cv {
        CellValue::Assigned(v) => !v.is_zero_vartime(),
        _ => false,
    }
}

fn unwrap<F: Field>(cv: &CellValue<F>) -> F {
    match *cv {
        CellValue::Assigned(f) => f,
        _ => panic!("the cell should be assigned"),
    }
}
