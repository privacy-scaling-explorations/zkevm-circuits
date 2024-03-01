mod scalar_field_element;
use scalar_field_element::ScalarFieldElement;

use crate::constants::{BITS, LIMBS, LOG_DEGREE};
use eth_types::U256;
use halo2_base::{
    gates::range::RangeConfig,
    utils::{fe_to_biguint, modulus},
};
use halo2_ecc::{
    bigint::CRTInteger,
    fields::{
        fp::{FpConfig, FpStrategy},
        FieldChip,
    },
    halo2_base::{AssignedValue, Context, ContextParams},
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    halo2curves::{bls12_381::Scalar, bn256::Fr, ff::PrimeField, pairing::Engine},
    plonk::ConstraintSystem,
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use itertools::Itertools;
use std::{iter, sync::LazyLock};

const BLOB_WIDTH: usize = 4096;
const LOG_BLOG_WIDTH: usize = 12;
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
    pub fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
        let scalar = FpConfig::configure(
            meta,
            FpStrategy::Simple,
            &[35],
            &[17],
            1,
            13,
            BITS,  // on
            LIMBS, //
            modulus::<Scalar>(),
            0,
            LOG_DEGREE.try_into().unwrap(),
        );

        Self { scalar }
    }

    // TODO: figure out why using this doesn't work?
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
                .iter()
                .zip_eq(blob.map(ScalarFieldElement::private))
                .map(|(root, f)| f * (root.clone() / (z.clone() - root.clone())).carry())
                .reduce(|a, b| (a + b).carry()) // TODO: can 4096 additions happen without overflow, yes but you need to add this in
                // a divide and conquer way. you need to add these in a tree like
                // manner so that it's clear to the context that the number of bits is not too
                // large....
                .unwrap()
                .carry()
            / blob_width;
        p.resolve(ctx, &self.scalar)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
