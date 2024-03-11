use eth_types::U256;
use halo2_base::{
    gates::range::RangeConfig,
    utils::{fe_to_biguint, modulus},
};
use halo2_ecc::{
    bigint::CRTInteger,
    fields::{fp::FpConfig, FieldChip},
    halo2_base::Context,
};
use halo2_proofs::{
    circuit::Value,
    halo2curves::{bls12_381::Scalar, bn256::Fr, ff::PrimeField},
};
use itertools::Itertools;
use std::{iter::successors, sync::LazyLock};

use crate::{
    blob::{BLOB_WIDTH, LOG_BLOG_WIDTH},
    constants::{BITS, LIMBS},
};

mod scalar_field_element;
use scalar_field_element::ScalarFieldElement;

pub static ROOTS_OF_UNITY: LazyLock<[Scalar; BLOB_WIDTH]> = LazyLock::new(|| {
    // https://github.com/ethereum/consensus-specs/blob/dev/specs/deneb/polynomial-commitments.md#constants
    let primitive_root_of_unity = Scalar::from(7);
    let modulus = U256::from_str_radix(Scalar::MODULUS, 16).unwrap();

    let exponent = (modulus - U256::one()) / U256::from(4096);
    let root_of_unity = primitive_root_of_unity.pow(&exponent.0);

    let ascending_order: Vec<_> = successors(Some(Scalar::one()), |x| Some(*x * root_of_unity))
        .take(BLOB_WIDTH)
        .collect();
    let bit_reversed_order: Vec<_> = (0..BLOB_WIDTH)
        .map(|i| {
            let j = u16::try_from(i).unwrap().reverse_bits() >> (16 - LOG_BLOG_WIDTH);
            ascending_order[usize::try_from(j).unwrap()]
        })
        .collect();
    bit_reversed_order.try_into().unwrap()
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

    pub fn assign2(
        &self,
        ctx: &mut Context<Fr>,
        blob: [Scalar; BLOB_WIDTH],
        // TODO: accept blob_digest as a 32-bytes parameter (instead of BLS scalar).
        z: Scalar,
        y: Scalar,
        /* blob_data_export: AssignedBlobDataExport */
    ) {
        // TODO:
        // blob_digest = keccak256(
        //     keccak256(metadata) ||
        //     keccak256(chunk[0].txdata) ||
        //     ... ||
        //     keccak256(chunk[MAX_AGG_SNARKS-1].txdata)
        // )
        //
        // We get the 32-bytes of digest from blob_data_export.challenge_digest:
        // refer: https://github.com/scroll-tech/zkevm-circuits/blob/feat/4844-blob-data-config/aggregator/src/aggregation/blob_data.rs#L52-L56
        //
        // We need to:
        // 1. assert equality of those 32 bytes (challenge digest)
        // 2. do blob_digest % BLS_MODULUS
        // 3. then load private
        let z_crt = self
            .scalar
            .load_private(ctx, Value::known(fe_to_biguint(&z).into()));

        let y_exp = self
            .scalar
            .load_private(ctx, Value::known(fe_to_biguint(&y).into()));

        let mut y_evl = self.scalar.load_constant(ctx, fe_to_biguint(&Fr::zero()));
        blob.iter()
            .zip_eq(ROOTS_OF_UNITY.map(|x| self.scalar.load_constant(ctx, fe_to_biguint(&x))))
            .for_each(|(blob_i, root_i_crt)| {
                let blob_i_crt = self
                    .scalar
                    .load_private(ctx, Value::known(fe_to_biguint(blob_i).into()));

                // TODO: assert that blob_i's limbs are equal to limbs from the bytes assigned in
                // BlobDataConfig.

                // a = int(polynomial[i]) * int(roots_of_unity_brp[i]) % BLS_MODULUS
                let a = self.scalar.mul(ctx, &blob_i_crt, &root_i_crt);

                // b = (int(BLS_MODULUS) + int(z) - int(roots_of_unity_brp[i])) % BLS_MODULUS
                let b = self.scalar.sub_no_carry(ctx, &z_crt, &root_i_crt);
                let b = self.scalar.carry_mod(ctx, &b);

                // y += int(div(a, b) % BLS_MODULUS)
                let a_by_b = self.scalar.divide(ctx, &a, &b);
                y_evl = self.scalar.add_no_carry(ctx, &y_evl, &a_by_b);
                y_evl = self.scalar.carry_mod(ctx, &y_evl);
            });

        let one = self.scalar.load_constant(ctx, fe_to_biguint(&Fr::one()));
        let blob_width = self
            .scalar
            .load_constant(ctx, fe_to_biguint(&Fr::from(BLOB_WIDTH as u64)));
        let z_to_blob_width = (0..LOG_BLOG_WIDTH).fold(z_crt, |acc, intermediate| {
            self.scalar.mul(ctx, &z_crt, &z_crt)
        });
        let z_to_blob_width_minus_one = self.scalar.sub_no_carry(ctx, &z_to_blob_width, &one);
        let z_to_blob_width_minus_one = self.scalar.carry_mod(ctx, &z_to_blob_width_minus_one);
        let factor = self
            .scalar
            .divide(ctx, &z_to_blob_width_minus_one, &blob_width);

        y_evl = self.scalar.mul(ctx, &y_evl, &factor);
        y_evl = self.scalar.carry_mod(ctx, &y_evl);

        self.scalar.assert_equal(ctx, &y_evl, &y_exp);
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
        let z_to_blob_width = successors(Some(z.clone()), |z| Some(z.clone() * z.clone()))
            .take(LOG_BLOG_WIDTH)
            .last()
            .unwrap();
        let p = (z_to_blob_width - one)
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
