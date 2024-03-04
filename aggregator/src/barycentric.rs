use halo2_base::{gates::range::RangeConfig, utils::modulus};
use halo2_ecc::{bigint::CRTInteger, fields::fp::FpConfig, halo2_base::Context};
use halo2_proofs::halo2curves::{bls12_381::Scalar, bn256::Fr, ff::PrimeField};
use itertools::Itertools;
use std::sync::LazyLock;

use crate::{
    blob::{BLOB_WIDTH, LOG_BLOG_WIDTH},
    constants::{BITS, LIMBS},
};

mod scalar_field_element;
use scalar_field_element::ScalarFieldElement;

static ROOTS_OF_UNITY: LazyLock<[Scalar; BLOB_WIDTH]> = LazyLock::new(|| {
    let primitive_root_of_unity = Scalar::ROOT_OF_UNITY.pow(&[2u64.pow(20), 0, 0, 0]);
    (0..BLOB_WIDTH)
        .scan(Scalar::one(), |root_of_unity, _| {
            *root_of_unity *= primitive_root_of_unity;
            Some(*root_of_unity)
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
});

#[derive(Clone, Debug)]
pub struct BarycentricEvaluationConfig {
    pub scalar: FpConfig<Fr, Scalar>,
}

impl BarycentricEvaluationConfig {
    pub fn construct(range: RangeConfig<Fr>) -> Self {
        Self {
            scalar: FpConfig::construct(range, BITS, LIMBS, modulus::<Scalar>()),
        }
    }

    pub fn assign(
        &self,
        ctx: &mut Context<Fr>,
        blob: [Scalar; BLOB_WIDTH],
        z: Scalar,
    ) -> CRTInteger<Fr> {
        let one = ScalarFieldElement::constant(Scalar::one());
        let blob_width = ScalarFieldElement::constant(u64::try_from(BLOB_WIDTH).unwrap().into());

        let z = ScalarFieldElement::private(z);
        let p = ((0..LOG_BLOG_WIDTH).fold(z.clone(), |square, _| square.clone() * square) - one)
            * ROOTS_OF_UNITY
                .map(ScalarFieldElement::constant)
                .into_iter()
                .zip_eq(blob.map(ScalarFieldElement::private))
                .map(|(root, f)| f * (root.clone() / (z.clone() - root)).carry())
                .sum()
            / blob_width;
        p.resolve(ctx, &self.scalar)
    }
}

pub fn interpolate(z: Scalar, coefficients: [Scalar; BLOB_WIDTH]) -> Scalar {
    let blob_width = u64::try_from(BLOB_WIDTH).unwrap();
    (z.pow(&[blob_width, 0, 0, 0]) - Scalar::one())
        * ROOTS_OF_UNITY
            .into_iter()
            .zip_eq(coefficients)
            .map(|(root, f)| f * root * (z - root).invert().unwrap())
            .sum::<Scalar>()
        * Scalar::from(blob_width).invert().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use eth_types::U256;
    use std::collections::BTreeSet;

    #[test]
    fn log_blob_width() {
        assert_eq!(2_usize.pow(LOG_BLOG_WIDTH.try_into().unwrap()), BLOB_WIDTH);
    }

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
            assert_eq!(
                root_of_unity.pow(&[BLOB_WIDTH.try_into().unwrap(), 0, 0, 0]),
                Scalar::one()
            );
        }
        assert_eq!(
            ROOTS_OF_UNITY.iter().collect::<BTreeSet<_>>().len(),
            BLOB_WIDTH
        );
    }
}
