//! Circuit to verify multiple ECDSA secp256k1 signatures.

// Naming notes:
// - *_be: Big-Endian bytes
// - *_le: Little-Endian bytes

use crate::{
    evm_circuit::util::{not, RandomLinearCombination, Word},
    table::KeccakTable,
    util::Expr,
};
use ecc::{EccConfig, GeneralEccChip};
use ecdsa::ecdsa::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
use eth_types::sign_types::{pk_bytes_le, pk_bytes_swap_endianness, SignData};
use eth_types::{self, Field};
use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use halo2_proofs::halo2curves::secp256k1::Secp256k1Affine;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    halo2curves::secp256k1,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use integer::{AssignedInteger, IntegerChip, IntegerConfig, IntegerInstructions, Range};

use itertools::Itertools;
use keccak256::plain::Keccak;
use log::error;
use maingate::{
    AssignedValue, MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig,
    RangeInstructions, RegionCtx,
};
use std::marker::PhantomData;

/// Power of randomness vector size required for the SignVerifyChip
pub const POW_RAND_SIZE: usize = 63;

/// Number of rows required for a verification of the SignVerifyChip in the
/// "signature address verify" region.
pub const VERIF_HEIGHT: usize = 1;

/// Auxiliary Gadget to verify a that a message hash is signed by the public
/// key corresponding to an Ethereum Address.
#[derive(Clone, Default, Debug)]
pub struct SignVerifyChip<F: Field, const MAX_VERIF: usize> {
    /// Aux generator for EccChip
    pub aux_generator: Secp256k1Affine,
    /// Window size for EccChip
    pub window_size: usize,
    /// Marker
    pub _marker: PhantomData<F>,
}

const NUMBER_OF_LIMBS: usize = 4;
const BIT_LEN_LIMB: usize = 72;

/// Return an expression that builds an integer element in the field from the
/// `bytes` in big endian.
fn int_from_bytes_be<F: Field>(bytes: &[Expression<F>]) -> Expression<F> {
    // sum_{i = 0}^{N} bytes[i] * 256^i
    let mut res = 0u8.expr();
    for (i, byte) in bytes.iter().rev().enumerate() {
        res = res + byte.clone() * Expression::Constant(F::from(256).pow(&[i as u64, 0, 0, 0]))
    }
    res
}

/// Constraint equality (using copy constraints) between `src` integer bytes and
/// `dst` integer bytes. Then assign the `dst` values from `src`.
fn copy_integer_bytes_le<F: Field>(
    region: &mut Region<'_, F>,
    name: &str,
    src: &[AssignedValue<F>; 32],
    dst: &[Column<Advice>; 32],
    offset: usize,
) -> Result<(), Error> {
    for (i, byte) in src.iter().enumerate() {
        let assigned_cell = region.assign_advice(
            || format!("{} byte {}", name, i),
            dst[i],
            offset,
            || byte.value().copied(),
        )?;
        region.constrain_equal(assigned_cell.cell(), byte.cell())?;
    }
    Ok(())
}

/// SignVerify Configuration
#[derive(Debug, Clone)]
pub(crate) struct SignVerifyConfig<F: Field> {
    q_enable: Selector,
    pk_hash: [Column<Advice>; 32],
    // When address is 0, we disable the signature verification by using a dummy pk, msg_hash and
    // signature which is not constrainted to match msg_hash_rlc nor the address.
    address: Column<Advice>,
    address_is_zero: IsZeroConfig<F>,
    address_inv: Column<Advice>,
    msg_hash_rlc: Column<Advice>,

    // ECDSA
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    // First 32 cells are coord x in little endian, following 32 cells are coord y in little
    // endian.
    pk: [[Column<Advice>; 32]; 2],
    msg_hash: [Column<Advice>; 32],
    power_of_randomness: [Expression<F>; POW_RAND_SIZE],

    // [is_enabled, input_rlc, input_len, output_rlc]
    keccak_table: KeccakTable,
}

impl<F: Field> SignVerifyConfig<F> {
    pub(crate) fn new(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; POW_RAND_SIZE],
        keccak_table: KeccakTable,
    ) -> Self {
        let q_enable = meta.complex_selector();

        let pk = [(); 2].map(|_| [(); 32].map(|_| meta.advice_column()));
        pk.iter()
            .for_each(|coord| coord.iter().for_each(|c| meta.enable_equality(*c)));

        let msg_hash = [(); 32].map(|_| meta.advice_column());
        msg_hash.iter().for_each(|c| meta.enable_equality(*c));

        let address = meta.advice_column();
        meta.enable_equality(address);

        let pk_hash = [(); 32].map(|_| meta.advice_column());

        let msg_hash_rlc = meta.advice_column();
        meta.enable_equality(msg_hash_rlc);

        let address_inv = meta.advice_column();
        let address_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(address, Rotation::cur()),
            address_inv,
        );
        // is_not_padding == address != 0
        let is_not_padding = not::expr(address_is_zero.is_zero_expression.clone());

        // Ref. spec SignVerifyChip 1. Verify that keccak(pub_key_bytes) = pub_key_hash
        // by keccak table lookup, where pub_key_bytes is built from the pub_key
        // in the ecdsa_chip
        // keccak lookup
        meta.lookup_any("keccak", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let selector = q_enable * is_not_padding.clone();
            let mut table_map = Vec::new();

            // Column 0: is_enabled
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            // Column 1: input_rlc (pk_rlc)
            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            let pk_le: [Expression<F>; 64] = pk
                .map(|coord| coord.map(|c| meta.query_advice(c, Rotation::cur())))
                .iter()
                .flatten()
                .cloned()
                .collect::<Vec<Expression<F>>>()
                .try_into()
                .expect("vector to array of size 64");
            let mut pk_be = pk_bytes_swap_endianness(&pk_le);
            pk_be.reverse();
            let pk_rlc =
                RandomLinearCombination::random_linear_combine_expr(pk_be, &power_of_randomness);
            table_map.push((selector.clone() * pk_rlc, keccak_input_rlc));

            // Column 2: input_len (64)
            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * 64usize.expr(), keccak_input_len));

            // Column 3: output_rlc (pk_hash_rlc)
            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            let mut pk_hash_rev = pk_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            pk_hash_rev.reverse(); // Ethereum decodes pk_hash into a Word as big endian, but
                                   // `random_linear_combine_expr` expects LSB first.
            let pk_hash_rlc = RandomLinearCombination::random_linear_combine_expr(
                pk_hash_rev,
                &power_of_randomness,
            );
            table_map.push((selector * pk_hash_rlc, keccak_output_rlc));

            table_map
        });

        // Ref. spec SignVerifyChip 2. Verify that the first 20 bytes of the
        // pub_key_hash equal the address
        meta.create_gate("address is pk_hash[-20:]", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let pk_hash = pk_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let address = meta.query_advice(address, Rotation::cur());

            let addr_from_pk = int_from_bytes_be(&pk_hash[32 - 20..]);

            vec![q_enable * (address - addr_from_pk)]
        });

        // Ref. spec SignVerifyChip 3. Verify that the signed message in the ecdsa_chip
        // with RLC encoding corresponds to msg_hash_rlc
        meta.create_gate("msg_hash_rlc = is_not_padding * RLC(msg_hash)", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let msg_hash = msg_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let msg_hash_rlc = meta.query_advice(msg_hash_rlc, Rotation::cur());

            let expected_msg_hash_rlc = RandomLinearCombination::random_linear_combine_expr(
                msg_hash,
                &power_of_randomness[..32],
            );
            vec![q_enable * (msg_hash_rlc - is_not_padding.clone() * expected_msg_hash_rlc)]
        });

        // ECDSA config
        let (rns_base, rns_scalar) =
            GeneralEccChip::<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
        let main_gate_config = MainGate::<F>::configure(meta);
        let mut overflow_bit_lengths: Vec<usize> = vec![];
        overflow_bit_lengths.extend(rns_base.overflow_lengths());
        overflow_bit_lengths.extend(rns_scalar.overflow_lengths());
        let range_config = RangeChip::<F>::configure(
            meta,
            &main_gate_config,
            vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS, 8],
            overflow_bit_lengths,
        );

        Self {
            q_enable,
            pk_hash,
            address,
            msg_hash_rlc,
            address_is_zero,
            address_inv,
            range_config,
            main_gate_config,
            pk,
            msg_hash,
            power_of_randomness,
            keccak_table,
        }
    }
}

pub(crate) struct KeccakAux {
    input: [u8; 64],
    output: [u8; 32],
}

impl<F: Field> SignVerifyConfig<F> {
    pub(crate) fn load_range(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let range_chip = RangeChip::<F>::new(self.range_config.clone());
        range_chip.load_table(layouter)
    }

    pub(crate) fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub(crate) fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

pub(crate) struct AssignedECDSA<F: Field> {
    pk_x_le: [AssignedValue<F>; 32],
    pk_y_le: [AssignedValue<F>; 32],
    msg_hash_le: [AssignedValue<F>; 32],
}

#[derive(Debug)]
pub(crate) struct AssignedSignatureVerify<F: Field> {
    pub(crate) address: AssignedCell<F, F>,
    pub(crate) msg_hash_rlc: AssignedCell<F, F>,
}

// Returns assigned constants [256^1, 256^2, .., 256^{n-1}]
fn assign_pows_256<F: Field>(
    ctx: &mut RegionCtx<'_, F>,
    main_gate: &MainGate<F>,
    n: usize,
) -> Result<Vec<AssignedValue<F>>, Error> {
    let mut pows = Vec::new();
    for i in 1..n {
        pows.push(main_gate.assign_constant(ctx, F::from(256).pow(&[i as u64, 0, 0, 0]))?);
    }
    Ok(pows)
}

// Return an array of bytes that corresponds to the little endian representation
// of the integer, adding the constraints to verify the correctness of the
// conversion (byte range check included).
fn integer_to_bytes_le<F: Field, FE: FieldExt>(
    ctx: &mut RegionCtx<'_, F>,
    range_chip: &RangeChip<F>,
    int: &AssignedInteger<FE, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
) -> Result<[AssignedValue<F>; 32], Error> {
    let (_, limb0_bytes) =
        range_chip.decompose(ctx, int.limbs()[0].as_ref().value().copied(), 8, 72)?;
    let (_, limb1_bytes) =
        range_chip.decompose(ctx, int.limbs()[1].as_ref().value().copied(), 8, 72)?;
    let (_, limb2_bytes) =
        range_chip.decompose(ctx, int.limbs()[2].as_ref().value().copied(), 8, 72)?;
    let (_, limb3_bytes) =
        range_chip.decompose(ctx, int.limbs()[3].as_ref().value().copied(), 8, 40)?;
    Ok(std::iter::empty()
        .chain(limb0_bytes)
        .chain(limb1_bytes)
        .chain(limb2_bytes)
        .chain(limb3_bytes)
        .collect_vec()
        .try_into()
        .unwrap())
}

/// Helper structure pass around references to all the chips required for an
/// ECDSA veficication.
struct ChipsRef<'a, F: Field, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize> {
    main_gate: &'a MainGate<F>,
    range_chip: &'a RangeChip<F>,
    ecc_chip: &'a GeneralEccChip<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    scalar_chip: &'a IntegerChip<secp256k1::Fq, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ecdsa_chip: &'a EcdsaChip<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

impl<F: Field, const MAX_VERIF: usize> SignVerifyChip<F, MAX_VERIF> {
    fn assign_aux(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        ecc_chip: &mut GeneralEccChip<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(), Error> {
        ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
        ecc_chip.assign_aux(ctx, self.window_size, 1)?;
        Ok(())
    }

    fn assign_ecdsa(
        &self,
        ctx: &mut RegionCtx<F>,
        chips: &ChipsRef<F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        sign_data: &SignData,
    ) -> Result<AssignedECDSA<F>, Error> {
        let SignData {
            signature,
            pk,
            msg_hash,
        } = sign_data;
        let (sig_r, sig_s) = signature;

        let ChipsRef {
            main_gate: _,
            range_chip,
            ecc_chip,
            scalar_chip,
            ecdsa_chip,
        } = chips;

        let integer_r = ecc_chip.new_unassigned_scalar(Value::known(*sig_r));
        let integer_s = ecc_chip.new_unassigned_scalar(Value::known(*sig_s));
        let msg_hash = ecc_chip.new_unassigned_scalar(Value::known(*msg_hash));

        let r_assigned = scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
        let s_assigned = scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
        let sig = AssignedEcdsaSig {
            r: r_assigned,
            s: s_assigned,
        };

        let pk_in_circuit = ecc_chip.assign_point(ctx, Value::known(*pk))?;
        let pk_assigned = AssignedPublicKey {
            point: pk_in_circuit,
        };
        let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;

        // Convert (msg_hash, pk_x, pk_y) integers to little endian bytes
        let msg_hash_le = integer_to_bytes_le(ctx, range_chip, &msg_hash)?;
        let pk_x = pk_assigned.point.x();
        let pk_x_le = integer_to_bytes_le(ctx, range_chip, pk_x)?;
        let pk_y = pk_assigned.point.y();
        let pk_y_le = integer_to_bytes_le(ctx, range_chip, pk_y)?;

        // Ref. spec SignVerifyChip 4. Verify the ECDSA signature
        ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)?;

        // TODO: Update once halo2wrong suports the following methods:
        // - `IntegerChip::assign_integer_from_bytes_le`
        // - `GeneralEccChip::assing_point_from_bytes_le`

        Ok(AssignedECDSA {
            pk_x_le,
            pk_y_le,
            msg_hash_le,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_signature_verify(
        &self,
        config: &SignVerifyConfig<F>,
        region: &mut Region<'_, F>,
        offset: usize,
        randomness: F,
        address_is_zero_chip: &IsZeroChip<F>,
        sign_data: Option<&SignData>,
        assigned_ecdsa: &AssignedECDSA<F>,
    ) -> Result<(AssignedSignatureVerify<F>, KeccakAux), Error> {
        let (padding, sign_data) = match sign_data {
            Some(sign_data) => (false, sign_data.clone()),
            None => (true, SignData::default()),
        };
        let SignData {
            signature: _,
            pk,
            msg_hash,
        } = sign_data;

        // Ref. spec SignVerifyChip 0. Copy constraints between pub_key and msg_hash
        // bytes of this chip and the ECDSA chip
        copy_integer_bytes_le(
            region,
            "pk_x",
            &assigned_ecdsa.pk_x_le,
            &config.pk[0],
            offset,
        )?;
        copy_integer_bytes_le(
            region,
            "pk_y",
            &assigned_ecdsa.pk_y_le,
            &config.pk[1],
            offset,
        )?;
        copy_integer_bytes_le(
            region,
            "msg_hash",
            &assigned_ecdsa.msg_hash_le,
            &config.msg_hash,
            offset,
        )?;

        config.q_enable.enable(region, offset)?;

        // Assign msg_hash_rlc
        let mut msg_hash_le = [0u8; 32];
        msg_hash_le
            .as_mut_slice()
            .copy_from_slice(msg_hash.to_bytes().as_slice());
        let msg_hash_rlc = Word::random_linear_combine(msg_hash_le, randomness);
        let msg_hash_rlc = if !padding { msg_hash_rlc } else { F::zero() };
        let msg_hash_rlc_assigned = region.assign_advice(
            || "msg_hash_rlc",
            config.msg_hash_rlc,
            offset,
            || Value::known(msg_hash_rlc),
        )?;

        // Assign pk
        let pk_le = pk_bytes_le(&pk);
        for (i, byte) in pk_le[..32].iter().enumerate() {
            region.assign_advice(
                || format!("pk x byte {}", i),
                config.pk[0][i],
                offset,
                || Value::known(F::from(*byte as u64)),
            )?;
        }
        for (i, byte) in pk_le[32..].iter().enumerate() {
            region.assign_advice(
                || format!("pk y byte {}", i),
                config.pk[1][i],
                offset,
                || Value::known(F::from(*byte as u64)),
            )?;
        }

        let pk_be = pk_bytes_swap_endianness(&pk_le);
        let mut keccak = Keccak::default();
        keccak.update(&pk_be);
        let pk_hash = keccak.digest();
        let address = pub_key_hash_to_address(&pk_hash);

        // Assign pk_hash
        let pk_hash = if !padding { pk_hash } else { vec![0u8; 32] };
        for (i, byte) in pk_hash.iter().enumerate() {
            region.assign_advice(
                || format!("pk_hash byte {}", i),
                config.pk_hash[i],
                offset,
                || Value::known(F::from(*byte as u64)),
            )?;
        }

        let address = if !padding { address } else { F::zero() };
        // Assign address and address_is_zero_chip
        let address_assigned = region.assign_advice(
            || "address",
            config.address,
            offset,
            || Value::known(address),
        )?;
        address_is_zero_chip.assign(region, offset, Value::known(address))?;

        // Assign msg_hash
        for (i, byte) in msg_hash_le.iter().enumerate() {
            region.assign_advice(
                || format!("msg_hash byte {}", i),
                config.msg_hash[i],
                offset,
                || Value::known(F::from(*byte as u64)),
            )?;
        }

        Ok((
            AssignedSignatureVerify {
                address: address_assigned,
                msg_hash_rlc: msg_hash_rlc_assigned,
            },
            KeccakAux {
                input: pk_be,
                output: pk_hash.try_into().expect("vec to array of size 32"),
            },
        ))
    }

    pub(crate) fn assign(
        &self,
        config: &SignVerifyConfig<F>,
        layouter: &mut impl Layouter<F>,
        randomness: F,
        signatures: &[SignData],
    ) -> Result<Vec<AssignedSignatureVerify<F>>, Error> {
        if signatures.len() > MAX_VERIF {
            error!(
                "signatures.len() = {} > MAX_VERIF = {}",
                signatures.len(),
                MAX_VERIF
            );
            return Err(Error::Synthesis);
        }
        let main_gate = MainGate::new(config.main_gate_config.clone());
        let range_chip = RangeChip::new(config.range_config.clone());
        let mut ecc_chip = GeneralEccChip::<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
            config.ecc_chip_config(),
        );
        let cloned_ecc_chip = ecc_chip.clone();
        let scalar_chip = cloned_ecc_chip.scalar_field_chip();

        layouter.assign_region(
            || "ecc chip aux",
            |region| self.assign_aux(&mut RegionCtx::new(region, 0), &mut ecc_chip),
        )?;

        let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
        let address_is_zero_chip = IsZeroChip::construct(config.address_is_zero.clone());

        let mut assigned_ecdsas = Vec::new();
        let mut keccak_auxs = Vec::new();

        let chips = ChipsRef {
            main_gate: &main_gate,
            range_chip: &range_chip,
            ecc_chip: &ecc_chip,
            scalar_chip,
            ecdsa_chip: &ecdsa_chip,
        };

        layouter.assign_region(
            || "ecdsa chip verification",
            |region| {
                assigned_ecdsas.clear();
                keccak_auxs.clear();
                let offset = &mut 0;
                let mut ctx = RegionCtx::new(region, *offset);
                for i in 0..MAX_VERIF {
                    let signature = if i < signatures.len() {
                        signatures[i].clone()
                    } else {
                        // padding (enabled when address == 0)
                        SignData::default()
                    };
                    let assigned_ecdsa = self.assign_ecdsa(&mut ctx, &chips, &signature)?;
                    assigned_ecdsas.push(assigned_ecdsa);
                }
                Ok(())
            },
        )?;

        let mut assigned_sig_verifs = Vec::new();
        layouter.assign_region(
            || "signature address verify",
            |mut region| {
                assigned_sig_verifs.clear();
                // for i in 0..MAX_VERIF
                for (i, assigned_ecdsa) in assigned_ecdsas.iter().enumerate() {
                    let sign_data = signatures.get(i); // None when padding (enabled when address == 0)
                    let (assigned_sig_verif, keccak_aux) = self.assign_signature_verify(
                        config,
                        &mut region,
                        i, // offset
                        randomness,
                        &address_is_zero_chip,
                        sign_data,
                        assigned_ecdsa,
                    )?;
                    if i < signatures.len() {
                        keccak_auxs.push(keccak_aux);
                    }
                    assigned_sig_verifs.push(assigned_sig_verif);
                }

                Ok(())
            },
        )?;
        Ok(assigned_sig_verifs)
    }
}

fn pub_key_hash_to_address<F: Field>(pk_hash: &[u8]) -> F {
    pk_hash[32 - 20..]
        .iter()
        .fold(F::zero(), |acc, b| acc * F::from(256) + F::from(*b as u64))
}

#[cfg(test)]
mod sign_verify_tests {
    use super::*;
    use crate::util::power_of_randomness_from_instance;
    use bus_mapping::circuit_input_builder::keccak_inputs_sign_verify;
    use eth_types::sign_types::sign;
    use halo2_proofs::arithmetic::Field as HaloField;
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        halo2curves::{
            bn256::Fr,
            group::{Curve, Group},
            CurveAffine,
        },
        plonk::Circuit,
    };
    use pretty_assertions::assert_eq;
    use rand::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[derive(Clone, Debug)]
    struct TestCircuitSignVerifyConfig<F: Field> {
        sign_verify: SignVerifyConfig<F>,
    }

    impl<F: Field> TestCircuitSignVerifyConfig<F> {
        pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
            let power_of_randomness = power_of_randomness_from_instance(meta);
            let keccak_table = KeccakTable::construct(meta);

            let sign_verify = SignVerifyConfig::new(meta, power_of_randomness, keccak_table);
            TestCircuitSignVerifyConfig { sign_verify }
        }
    }

    #[derive(Default)]
    struct TestCircuitSignVerify<F: Field, const MAX_VERIF: usize> {
        sign_verify: SignVerifyChip<F, MAX_VERIF>,
        randomness: F,
        signatures: Vec<SignData>,
    }

    impl<F: Field, const MAX_VERIF: usize> Circuit<F> for TestCircuitSignVerify<F, MAX_VERIF> {
        type Config = TestCircuitSignVerifyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            TestCircuitSignVerifyConfig::new(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            self.sign_verify.assign(
                &config.sign_verify,
                &mut layouter,
                self.randomness,
                &self.signatures,
            )?;
            config.sign_verify.keccak_table.dev_load(
                &mut layouter,
                &keccak_inputs_sign_verify(&self.signatures),
                self.randomness,
            )?;
            config.sign_verify.load_range(&mut layouter)?;
            Ok(())
        }
    }

    fn run<F: Field, const MAX_VERIF: usize>(k: u32, signatures: Vec<SignData>) {
        let mut rng = XorShiftRng::seed_from_u64(2);
        let aux_generator =
            <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();

        let randomness = F::random(&mut rng);
        let mut power_of_randomness: Vec<Vec<F>> = (1..POW_RAND_SIZE + 1)
            .map(|exp| {
                vec![randomness.pow(&[exp as u64, 0, 0, 0]); signatures.len() * VERIF_HEIGHT]
            })
            .collect();
        // SignVerifyChip -> ECDSAChip -> MainGate instance column
        power_of_randomness.push(vec![]);
        let circuit = TestCircuitSignVerify::<F, MAX_VERIF> {
            sign_verify: SignVerifyChip {
                aux_generator,
                window_size: 2,
                _marker: PhantomData,
            },
            randomness,
            signatures,
        };

        let prover = match MockProver::run(k, &circuit, power_of_randomness) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    // Generate a test key pair
    fn gen_key_pair(rng: impl RngCore) -> (secp256k1::Fq, Secp256k1Affine) {
        // generate a valid signature
        let generator = Secp256k1Affine::generator();
        let sk = secp256k1::Fq::random(rng);
        let pk = generator * sk;
        let pk = pk.to_affine();

        (sk, pk)
    }

    // Generate a test message hash
    fn gen_msg_hash(rng: impl RngCore) -> secp256k1::Fq {
        secp256k1::Fq::random(rng)
    }

    // Returns (r, s)
    fn sign_with_rng(
        rng: impl RngCore,
        sk: secp256k1::Fq,
        msg_hash: secp256k1::Fq,
    ) -> (secp256k1::Fq, secp256k1::Fq) {
        let randomness = secp256k1::Fq::random(rng);
        sign(randomness, sk, msg_hash)
    }

    // High memory usage test.  Run in serial with:
    // `cargo test [...] serial_ -- --ignored --test-threads 1`
    #[ignore]
    #[test]
    fn serial_test_sign_verify() {
        // Vectors using `XorShiftRng::seed_from_u64(1)`
        // sk: 0x771bd7bf6c6414b9370bb8559d46e1cedb479b1836ea3c2e59a54c343b0d0495
        // pk: (
        //   0x8e31a3586d4c8de89d4e0131223ecfefa4eb76215f68a691ae607757d6256ede,
        //   0xc76fdd462294a7eeb8ff3f0f698eb470f32085ba975801dbe446ed8e0b05400b
        // )
        // pk_hash: d90e2e9d267cbcfd94de06fa7adbe6857c2c733025c0b8938a76beeefc85d6c7
        // addr: 0x7adbe6857c2c733025c0b8938a76beeefc85d6c7
        let mut rng = XorShiftRng::seed_from_u64(1);
        const MAX_VERIF: usize = 3;
        const NUM_SIGS: usize = 2;
        let mut signatures = Vec::new();
        for _ in 0..NUM_SIGS {
            let (sk, pk) = gen_key_pair(&mut rng);
            let msg_hash = gen_msg_hash(&mut rng);
            let sig = sign_with_rng(&mut rng, sk, msg_hash);
            signatures.push(SignData {
                signature: sig,
                pk,
                msg_hash,
            });
        }

        let k = 19;
        run::<Fr, MAX_VERIF>(k, signatures);
    }
}
