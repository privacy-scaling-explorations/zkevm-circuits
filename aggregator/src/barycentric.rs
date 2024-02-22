use eth_types::U256;
use halo2_proofs::halo2curves::{bls12_381::Scalar, ff::PrimeField};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_field_modulus() {
        let bls_modulus = U256::from_str_radix(Scalar::MODULUS, 16).unwrap();
        // BLS_MODULUS as decimal string from https://eips.ethereum.org/EIPS/eip-4844.
        let expected_bls_modulus = U256::from_str_radix(
            "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            10,
        )
        .unwrap();
        assert_eq!(bls_modulus, expected_bls_modulus);
    }
}
