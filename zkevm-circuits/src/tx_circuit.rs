// TODO Remove this
#![allow(missing_docs)]
// TODO Remove this
#![allow(unused_imports)]

use group::{ff::Field, prime::PrimeCurveAffine, Curve};
use std::{marker::PhantomData, os::unix::prelude::FileTypeExt};

use ecc::{EccConfig, GeneralEccChip};
use ecdsa::ecdsa::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip, EcdsaConfig};
use integer::{IntegerInstructions, NUMBER_OF_LOOKUP_LIMBS};
use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions, RegionCtx};
use pairing::arithmetic::FieldExt;
use secp256k1::Secp256k1Affine;

use crate::gadget::is_zero::{IsZeroChip, IsZeroConfig};
use halo2_proofs::{
    arithmetic::{BaseExt, CurveAffine},
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

// TODO: Move these utils outside of `evm_circuit` so that they can be used by
// other circuits without crossing boundaries.
use crate::evm_circuit::util::{
    and, constraint_builder::BaseConstraintBuilder, not, or, select, RandomLinearCombination,
};
use crate::util::Expr;

/// Auxiliary Gadget to verify a that a message hash is signed by the public
/// key corresponding to an Ethereum Address.
struct SignVerifyChip<F: FieldExt> {
    ecdsa_chip: EcdsaChip<Secp256k1Affine, F>,
}

const KECCAK_IS_ENABLED: usize = 0;
const KECCAK_INPUT_RLC: usize = 0;
const KECCAK_INPUT_LEN: usize = 0;
const KECCAK_OUTPUT_RLC: usize = 0;

struct SignVerifyConfig<F: FieldExt> {
    pub_key_hash: [Column<Advice>; 32],
    address: Column<Advice>,
    msg_hash_rlc: Column<Advice>,
    msg_hash_rlc_is_zero: IsZeroConfig<F>,
    msg_hash_rlc_inv: Column<Advice>,

    // ECDSA
    ecdsa_config: EcdsaConfig,
    // signature: [[Column<Advice>; 32]; 2],
    pub_key: [Column<Advice>; 32 * 2],
    msg_hash: [Column<Advice>; 32],

    power_of_randomness: [Expression<F>; 63],

    // [is_enabled, input_rlc, input_len, output_rlc]
    keccak_table: [Column<Advice>; 4],
}

impl<F: FieldExt> SignVerifyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; 63],
    ) -> SignVerifyConfig<F> {
        // create ecdsa config
        const BIT_LEN_LIMB: usize = 68;
        let (rns_base, rns_scalar) = GeneralEccChip::<Secp256k1Affine, F>::rns(BIT_LEN_LIMB);
        let main_gate_config = MainGate::<F>::configure(meta);
        let mut overflow_bit_lengths: Vec<usize> = vec![];
        overflow_bit_lengths.extend(rns_base.overflow_lengths());
        overflow_bit_lengths.extend(rns_scalar.overflow_lengths());
        let range_config = RangeChip::<F>::configure(meta, &main_gate_config, overflow_bit_lengths);

        let ecdsa_config = EcdsaConfig::new(range_config, main_gate_config);
        let pub_key = [(); 32 * 2].map(|_| meta.advice_column());
        let msg_hash = [(); 32].map(|_| meta.advice_column());

        // create address, msg_hash, pub_key_hash, and msg_hash_inv, and iz_zero

        let address = meta.advice_column();
        let pub_key_hash = [(); 32].map(|_| meta.advice_column());

        let msg_hash_rlc = meta.advice_column();

        // is_enabled === msg_hash_rlc != 0

        let msg_hash_rlc_inv = meta.advice_column();
        let msg_hash_rlc_is_zero = IsZeroChip::configure(
            meta,
            |_| Expression::Constant(F::one()), // always activate
            |virtual_cells| virtual_cells.query_advice(msg_hash_rlc, Rotation::cur()),
            msg_hash_rlc_inv, // helper column used internally?
        );
        let is_enabled = not::expr(msg_hash_rlc_is_zero.is_zero_expression.clone());

        // lookup keccak table

        let keccak_table = [(); 4].map(|_| meta.advice_column());

        // keccak lookup
        meta.lookup_any("keccak", |meta| {
            let mut table_map = Vec::new();

            // Column 0: is_enabled
            let keccak_is_enabled =
                meta.query_advice(keccak_table[KECCAK_IS_ENABLED], Rotation::cur());
            table_map.push((is_enabled.clone(), keccak_is_enabled));

            // Column 1: input_rlc (pub_key_rlc)
            let keccak_input_rlc =
                meta.query_advice(keccak_table[KECCAK_INPUT_RLC], Rotation::cur());
            let pub_key = pub_key.map(|c| meta.query_advice(c, Rotation::cur()));
            let pub_key_rlc =
                RandomLinearCombination::random_linear_combine_expr(pub_key, &power_of_randomness);
            table_map.push((is_enabled.clone() * pub_key_rlc, keccak_input_rlc));

            // Column 2: input_len (64)
            let keccak_input_len =
                meta.query_advice(keccak_table[KECCAK_INPUT_LEN], Rotation::cur());
            table_map.push((is_enabled.clone() * 64usize.expr(), keccak_input_len));

            // Column 3: output_rlc (pub_key_hash_rlc)
            let keccak_output_rlc =
                meta.query_advice(keccak_table[KECCAK_OUTPUT_RLC], Rotation::cur());
            let pub_key_hash = pub_key_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let pub_key_hash_rlc = RandomLinearCombination::random_linear_combine_expr(
                pub_key_hash,
                &power_of_randomness,
            );
            table_map.push((is_enabled.clone() * pub_key_hash_rlc, keccak_output_rlc));

            table_map
        });

        SignVerifyConfig {
            pub_key_hash,
            address,
            msg_hash_rlc,
            msg_hash_rlc_is_zero,
            msg_hash_rlc_inv,
            ecdsa_config,
            pub_key,
            msg_hash,
            power_of_randomness,
            keccak_table,
        }
    }

    /*
    pub fn assign(
        mut layouter: impl Layouter<F>,
        config: Self::Config,
        randomness: F,
        txs: &[TxSignData],
    ) -> Result<(), Error> {
        Ok(())
    }

    pub fn assign_tx(
        mut layouter: impl Layouter<F>,
        config: Self::Config,
        randomness: F,
        tx: &TxSignData,
    ) -> Result<(), Error> {
        Ok(())
    }
    */

    /*
        pub fn load_tables(config: &SignVerifyConfig<F>, layouter: &mut impl Layouter<F>) {
            use ecdsa::maingate::RangeInstructions;
            const BIT_LEN_LIMB: usize = 68;
            use ecdsa::integer::NUMBER_OF_LOOKUP_LIMBS;

            let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
            let range_chip = RangeChip::<F>::new(config.range_config.clone(), bit_len_lookup).unwrap();
            range_chip.load_limb_range_table(layouter).unwrap();
            range_chip.load_overflow_range_tables(layouter).unwrap();
       }
    */
}

struct TxSignData {
    signature: (secp256k1::Fq, secp256k1::Fq),
    pub_key: Secp256k1Affine,
    msg_hash: secp256k1::Fq,
}

/*
pub trait SignVerifyInstruction<F: FieldExt> {
    fn check(pub_key_hash: Vec<u8>, address: F, msg_hash_rlc: F, random: F) -> Result<(), Error>;
}
*/

#[cfg(test)]
mod sign_verify_tets {
    use super::*;
    use group::Group;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::Fr;
    use rand::RngCore;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    const BIT_LEN_LIMB: usize = 68;

    #[derive(Clone, Debug)]
    struct TestCircuitSignVerifyConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
    }

    impl TestCircuitSignVerifyConfig {
        pub fn new<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
            let (rns_base, rns_scalar) = GeneralEccChip::<Secp256k1Affine, F>::rns(BIT_LEN_LIMB);
            let main_gate_config = MainGate::<F>::configure(meta);
            let mut overflow_bit_lengths: Vec<usize> = vec![];
            overflow_bit_lengths.extend(rns_base.overflow_lengths());
            overflow_bit_lengths.extend(rns_scalar.overflow_lengths());
            let range_config =
                RangeChip::<F>::configure(meta, &main_gate_config, overflow_bit_lengths);
            TestCircuitSignVerifyConfig {
                main_gate_config,
                range_config,
            }
        }

        pub fn ecc_chip_config(&self) -> EccConfig {
            EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
        }

        pub fn config_range<F: FieldExt>(
            &self,
            layouter: &mut impl Layouter<F>,
        ) -> Result<(), Error> {
            let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
            let range_chip = RangeChip::<F>::new(self.range_config.clone(), bit_len_lookup);
            range_chip.load_limb_range_table(layouter)?;
            range_chip.load_overflow_range_tables(layouter)?;

            Ok(())
        }
    }

    #[derive(Default)]
    struct TestCircuitSignVerify<F: FieldExt> {
        aux_generator: Secp256k1Affine,
        window_size: usize,
        txs: Vec<TxSignData>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitSignVerify<F> {
        type Config = TestCircuitSignVerifyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            TestCircuitSignVerifyConfig::new::<F>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut ecc_chip =
                GeneralEccChip::<Secp256k1Affine, F>::new(config.ecc_chip_config(), BIT_LEN_LIMB);
            let scalar_chip = ecc_chip.scalar_field_chip();

            // Only using 1 signature for now
            let TxSignData {
                signature,
                pub_key,
                msg_hash,
            } = self.txs[0];
            let (sig_s, sig_r) = signature;
            let pk = pub_key;

            layouter.assign_region(
                || "assign aux values",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    ecc_chip.assign_aux_generator(ctx, Some(self.aux_generator))?;
                    ecc_chip.assign_aux(ctx, self.window_size, 1)?;
                    Ok(())
                },
            )?;

            let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());

            layouter.assign_region(
                || "ecdsa chip verification",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let integer_r = ecc_chip.new_unassigned_scalar(Some(sig_r));
                    let integer_s = ecc_chip.new_unassigned_scalar(Some(sig_s));
                    let msg_hash = ecc_chip.new_unassigned_scalar(Some(msg_hash));

                    let r_assigned = scalar_chip.assign_integer(ctx, integer_r)?;
                    let s_assigned = scalar_chip.assign_integer(ctx, integer_s)?;
                    let sig = AssignedEcdsaSig {
                        r: r_assigned,
                        s: s_assigned,
                    };

                    let pk_in_circuit = ecc_chip.assign_point(ctx, Some(pk.into()))?;
                    let pk_assigned = AssignedPublicKey {
                        point: pk_in_circuit,
                    };
                    let msg_hash = scalar_chip.assign_integer(ctx, msg_hash)?;
                    ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)
                },
            )?;

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    fn run<F: FieldExt>(txs: Vec<TxSignData>) {
        let k = 20;
        let mut rng = XorShiftRng::seed_from_u64(2);
        let aux_generator =
            <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();
        let circuit = TestCircuitSignVerify::<F> {
            aux_generator,
            window_size: 2,
            txs,
            _marker: PhantomData,
        };

        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    // Generate a test key pair
    fn gen_key_pair(rng: impl RngCore) -> (secp256k1::Fq, Secp256k1Affine) {
        // generate a valid signature
        let generator = <Secp256k1Affine as PrimeCurveAffine>::generator();
        let sk = <Secp256k1Affine as CurveAffine>::ScalarExt::random(rng);
        let pk = generator * sk;
        let pk = pk.to_affine();

        (sk, pk)
    }

    // Generate a test message hash
    fn gen_msg_hash(rng: impl RngCore) -> secp256k1::Fq {
        <Secp256k1Affine as CurveAffine>::ScalarExt::random(rng)
    }

    // Returns (r, s)
    fn sign(
        rng: impl RngCore,
        sk: secp256k1::Fq,
        msg_hash: secp256k1::Fq,
    ) -> (secp256k1::Fq, secp256k1::Fq) {
        let randomness = <Secp256k1Affine as CurveAffine>::ScalarExt::random(rng);
        let randomness_inv = randomness.invert().unwrap();
        let generator = <Secp256k1Affine as PrimeCurveAffine>::generator();
        let sig_point = generator * randomness;
        let x = sig_point.to_affine().coordinates().unwrap().x().clone();

        let x_repr = &mut Vec::with_capacity(32);
        x.write(x_repr).unwrap();

        let mut x_bytes = [0u8; 64];
        x_bytes[..32].copy_from_slice(&x_repr[..]);

        let x_bytes_on_n = <Secp256k1Affine as CurveAffine>::ScalarExt::from_bytes_wide(&x_bytes); // get x cordinate (E::Base) on E::Scalar
        let sig_s = randomness_inv * (msg_hash + x_bytes_on_n * sk);
        (x_bytes_on_n, sig_s)
    }

    #[test]
    fn test_sign_verify() {
        let mut rng = XorShiftRng::seed_from_u64(1);
        let (sk, pk) = gen_key_pair(&mut rng);
        let msg_hash = gen_msg_hash(&mut rng);
        let sig = sign(&mut rng, sk, msg_hash);

        let txs = vec![TxSignData {
            signature: sig,
            pub_key: pk,
            msg_hash: msg_hash,
        }];

        // generate a valid signature

        run::<Fr>(txs);
    }
}
