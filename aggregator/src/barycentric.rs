use eth_types::U256;
use halo2_proofs::halo2curves::{bls12_381::Scalar, ff::PrimeField};
use std::{iter, sync::LazyLock};

static ROOTS_OF_UNITY: LazyLock<[Scalar; 4096]> = LazyLock::new(|| {
    let primitive_root_of_unity = Scalar::ROOT_OF_UNITY.pow(&[2u64.pow(20), 0, 0, 0]);
    (0..4096)
        .scan(Scalar::one(), |root_of_unity, _| {
            *root_of_unity = *root_of_unity * primitive_root_of_unity;
            Some(*root_of_unity)
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
});

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

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

    #[test]
    fn roots_of_unity() {
        for root_of_unity in ROOTS_OF_UNITY.iter() {
            assert_eq!(root_of_unity.pow(&[4096, 0, 0, 0]), Scalar::one());
        }
        assert_eq!(ROOTS_OF_UNITY.iter().collect::<BTreeSet<_>>().len(), 4096);
    }
}
