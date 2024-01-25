//! Circuit to verify multiple ECDSA secp256k1 signatures.

// Naming notes:
// - *_be: Big-Endian bytes
// - *_le: Little-Endian bytes
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
mod dev;
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
mod test;

use crate::{
    evm_circuit::{
        util::{from_bytes, not, rlc},
        EvmCircuit,
    },
    keccak_circuit::KeccakCircuit,
    table::{KeccakTable, SigTable},
    util::{word::Word, Challenges, Expr, SubCircuit, SubCircuitConfig},
};
use ecc::{maingate, EccConfig, GeneralEccChip};
use ecdsa::ecdsa::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
use eth_types::{
    self, keccak256,
    sign_types::{pk_bytes_le, pk_bytes_swap_endianness, SignData},
    Field,
};
use halo2_proofs::{
    circuit::{AssignedCell, Cell, Layouter, Value},
    halo2curves::{ff::PrimeField, secp256k1, secp256k1::Secp256k1Affine},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, SecondPhase, Selector},
    poly::Rotation,
};
use integer::{AssignedInteger, IntegerChip, IntegerInstructions, Range};

use itertools::Itertools;
use log::error;
use maingate::{
    AssignedValue, MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig,
    RangeInstructions, RegionCtx,
};
use num::Integer;
use std::{iter, marker::PhantomData};

mod utils;
use utils::*;
/// Auxiliary Gadget to verify a that a message hash is signed by the public
/// key corresponding to an Ethereum Address.
#[derive(Clone, Debug)]
pub struct SigCircuit<F: Field> {
    /// Signatures
    pub signatures: Vec<SignData>,
    /// Aux generator for EccChip
    pub aux_generator: Secp256k1Affine,
    /// Window size for EccChip
    pub window_size: usize,
    /// Max number of verifications
    pub max_verif: usize,
    /// Marker
    pub _marker: PhantomData<F>,
}

impl<F: Field> SubCircuit<F> for SigCircuit<F> {
    type Config = SigCircuitConfig<F>;

    fn new_from_block(block: &crate::witness::Block<F>) -> Self {
        assert!(block.circuits_params.max_txs <= MAX_NUM_SIG);

        SigCircuit {
            signatures: block.get_sign_data(true),
            aux_generator: Secp256k1Affine::default(),
            window_size: 4,
            max_verif: MAX_NUM_SIG,
            _marker: Default::default(),
        }
    }

    // Since sig circuit / halo2-lib use vertical cell assignment,
    // so the returned pair is consisted of same values
    fn min_num_rows_block(block: &crate::witness::Block<F>) -> (usize, usize) {
        let ecdsa_verif_count =
            block.txs.iter().count() + block.precompile_events.get_ecrecover_events().len();
        // Reserve one ecdsa verification for padding tx such that the bad case in which some tx
        // calls MAX_NUM_SIG - 1 ecrecover precompile won't happen. If that case happens, the sig
        // circuit won't have more space for the padding tx's ECDSA verification. Then the
        // prover won't be able to produce any valid proof.
        let max_num_verif = MAX_NUM_SIG - 1;

        let row_num = if block.circuits_params.max_vertical_circuit_rows == 0 {
            Self::min_num_rows(ecdsa_verif_count)
        } else {
            block.circuits_params.max_vertical_circuit_rows
        };
        // Instead of showing actual minimum row usage,
        // halo2-lib based circuits use min_row_num to represent a percentage of total-used capacity
        // This functionality allows l2geth to decide if additional ops can be added.
        let min_row_num = (row_num / max_num_verif) * ecdsa_verif_count;

        (min_row_num, row_num)
    }

    /// Returns number of unusable rows of the SubCircuit, which should be
    /// `meta.blinding_factors() + 1`.
    fn unusable_rows() -> usize {
        [
            KeccakCircuit::<F>::unusable_rows(),
            EvmCircuit::<F>::unusable_rows(),
            // may include additional subcircuits here
        ]
        .into_iter()
        .max()
        .unwrap()
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load_range(layouter)?;
        self.assign(config, layouter, &self.signatures, challenges)?;
        Ok(())
    }
}

impl<F: Field> Default for SigCircuit<F> {
    fn default() -> Self {
        Self {
            signatures: vec![],
            aux_generator: Secp256k1Affine::default(),
            window_size: 4,
            max_verif: 0,
            _marker: PhantomData::default(),
        }
    }
}

const NUMBER_OF_LIMBS: usize = 4;
const BIT_LEN_LIMB: usize = 72;
const BIT_LEN_LAST_LIMB: usize = 256 - (NUMBER_OF_LIMBS - 1) * BIT_LEN_LIMB;

/// Arguments accepted to configure the EccCircuitConfig.
#[derive(Clone, Debug)]
pub struct SigCircuitConfigArgs<F: Field> {
    /// SigTable
    sig_table: SigTable,
    /// Keccak
    keccak_table: KeccakTable,

    /// zkEVM challenge API.
    pub challenges: Challenges<Expression<F>>,
}

/// SignVerify Configuration
#[derive(Debug, Clone)]
pub struct SigCircuitConfig<F: Field> {
    // ECDSA
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    // RLC
    q_rlc_keccak_input: Selector,
    rlc: Column<Advice>,
    /// SigTable
    sig_table: SigTable,
    // Keccak
    q_keccak: Selector,
    _keccak_table: KeccakTable,

    _marker: PhantomData<F>,
}

impl<F: Field> SubCircuitConfig<F> for SigCircuitConfig<F> {
    type ConfigArgs = SigCircuitConfigArgs<F>;

    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            sig_table,
            keccak_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        // ECDSA config
        let (rns_base, rns_scalar) =
            GeneralEccChip::<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
        let main_gate_config = MainGate::<F>::configure(meta);
        let range_config = RangeChip::<F>::configure(
            meta,
            &main_gate_config,
            vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS, 8],
            [rns_base.overflow_lengths(), rns_scalar.overflow_lengths()].concat(),
        );

        // RLC
        let q_rlc_keccak_input = meta.selector();
        let rlc = meta.advice_column_in(SecondPhase);
        meta.enable_equality(rlc);

        Self::configure_rlc(
            meta,
            "keccak_input_rlc",
            main_gate_config.clone(),
            q_rlc_keccak_input,
            rlc,
            challenges.keccak_input(),
        );

        // sig_table
        meta.enable_equality(sig_table.recovered_addr);
        meta.enable_equality(sig_table.sig_r.lo());
        meta.enable_equality(sig_table.sig_r.hi());
        meta.enable_equality(sig_table.sig_s.lo());
        meta.enable_equality(sig_table.sig_s.hi());
        meta.enable_equality(sig_table.sig_v);
        meta.enable_equality(sig_table.is_valid);
        meta.enable_equality(sig_table.msg_hash.lo());
        meta.enable_equality(sig_table.msg_hash.hi());

        // Ref. spec SigCircuit 1. Verify that keccak(pub_key_bytes) = pub_key_hash
        // by keccak table lookup, where pub_key_bytes is built from the pub_key
        // in the ecdsa_chip.
        let q_keccak = meta.complex_selector();
        meta.lookup_any("keccak", |meta| {
            // When address is 0, we disable the signature verification by using a dummy pk,
            // msg_hash and signature which is not constrained to match msg_hash nor the address.
            // Layout:
            // | q_keccak |        a        |    b     |     c     |   rlc   |
            // | -------- | --------------- |--------- | --------- | ------- |
            // |     1    |   is_addr_zero  | word_lo  |  word_hi  |  pk_rlc |
            let q_keccak = meta.query_selector(q_keccak);
            let is_address_zero = meta.query_advice(main_gate_config.advices()[0], Rotation::cur());
            let is_enable = q_keccak * not::expr(is_address_zero);
            let word_lo = meta.query_advice(main_gate_config.advices()[1], Rotation::cur());
            let word_hi = meta.query_advice(main_gate_config.advices()[2], Rotation::cur());
            let input = [
                is_enable.clone(),
                is_enable.clone() * meta.query_advice(rlc, Rotation::cur()),
                is_enable.clone() * 64usize.expr(),
                is_enable.clone() * word_lo,
                is_enable * word_hi,
            ];
            let table = [
                keccak_table.is_enabled,
                keccak_table.input_rlc,
                keccak_table.input_len,
                keccak_table.output.lo(),
                keccak_table.output.hi(),
            ]
            .map(|column| meta.query_advice(column, Rotation::cur()));

            input.into_iter().zip(table).collect()
        });

        Self {
            range_config,
            main_gate_config,
            q_rlc_keccak_input,
            rlc,
            q_keccak,
            _keccak_table: keccak_table,
            sig_table,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> SigCircuitConfig<F> {
    fn configure_rlc(
        meta: &mut ConstraintSystem<F>,
        name: &'static str,
        main_gate_config: MainGateConfig,
        q_rlc: Selector,
        rlc: Column<Advice>,
        challenge: Expression<F>,
    ) {
        // Layout (take input with length 12 as an example)
        // | q_rlc |                          rlc                        |   a   |   b   |   c   |
        // d    |   e    | | ----- | --------------------------------------------------- |
        // ----- | ----- | ----- | ------ | ------ | |   1   |
        // 0 |     0 |     0 |     0 |  be[0] |  be[1] | |   1   |
        // be[0]*r^1 +  be[1] | be[2] | be[3] | be[4] |  be[5] |  be[6] | |   1   | be[0]*
        // r^6  + be[1]*r^5  + ... +  be[5]*r^1 +  be[6] | be[7] | be[8] | be[9] | be[10] | be[11] |
        // |   0   | be[0]*r^11 + be[1]*r^10 + ... + be[10]*r^1 + be[11] |       |       |       |
        // |        |
        //
        // Note that the first row of zeros will be enforced by copy constraint.
        meta.create_gate(name, |meta| {
            let q_rlc = meta.query_selector(q_rlc);
            let [a, b, c, d, e] = main_gate_config
                .advices()
                .map(|column| meta.query_advice(column, Rotation::cur()));
            let [rlc, rlc_next] = [Rotation::cur(), Rotation::next()]
                .map(|rotation| meta.query_advice(rlc, rotation));
            let inputs = [e, d, c, b, a, rlc];

            vec![q_rlc * (rlc_next - rlc::expr(&inputs, challenge))]
        });
    }

    pub(crate) fn load_range(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let range_chip = RangeChip::<F>::new(self.range_config.clone());
        range_chip.load_table(layouter)
    }

    pub(crate) fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

/// Term provides a wrapper of possible assigned cell with value or unassigned
/// value. It's similar to `AssignedCell` but with explicitly set value.
///
/// The reason to use `Term` instead of `AssignedCell` is because the value of
/// `AssignedCell` will always be `Value::unknown()` if the columns is not in
/// current phase, even the value assigned is not. And this behavior is due to
/// the fact that the `to` function in `assign_fixed` and `assign_advice` is
/// `FnMut` and will be guaranteed to be only called once.
#[derive(Clone, Debug)]
pub(crate) enum Term<F> {
    Assigned(Cell, Value<F>),
    _Unassigned(Value<F>),
}

impl<F: Field> Term<F> {
    fn assigned(cell: Cell, value: Value<F>) -> Self {
        Self::Assigned(cell, value)
    }

    fn cell(&self) -> Option<Cell> {
        match self {
            Self::Assigned(cell, _) => Some(*cell),
            Self::_Unassigned(_) => None,
        }
    }

    fn value(&self) -> Value<F> {
        match self {
            Self::Assigned(_, value) => *value,
            Self::_Unassigned(value) => *value,
        }
    }
}

pub(crate) struct AssignedECDSA<F: Field> {
    pk_x_le: [AssignedValue<F>; 32],
    pk_y_le: [AssignedValue<F>; 32],
    msg_hash_le: [AssignedValue<F>; 32],

    r_le: [AssignedValue<F>; 32],
    s_le: [AssignedValue<F>; 32],
    v: AssignedValue<F>,
}

#[derive(Debug)]
pub(crate) struct AssignedSignatureVerify<F: Field> {
    pub(crate) address: AssignedValue<F>,
    pub(crate) msg_hash: Word<AssignedValue<F>>,

    r: Word<AssignedValue<F>>,
    s: Word<AssignedValue<F>>,
    v: AssignedValue<F>,

    is_valid: AssignedValue<F>,
}

// Return an array of bytes that corresponds to the little endian representation
// of the integer, adding the constraints to verify the correctness of the
// conversion (byte range check included).
fn integer_to_bytes_le<F: Field, FE: PrimeField>(
    ctx: &mut RegionCtx<'_, F>,
    range_chip: &RangeChip<F>,
    int: &AssignedInteger<FE, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
) -> Result<[AssignedValue<F>; 32], Error> {
    let bytes = int
        .limbs()
        .iter()
        .zip_eq([BIT_LEN_LIMB, BIT_LEN_LIMB, BIT_LEN_LIMB, BIT_LEN_LAST_LIMB])
        .map(|(limb, bit_len)| {
            range_chip
                .decompose(ctx, limb.as_ref().value().copied(), 8, bit_len)
                .map(|(_, byte)| byte)
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect_vec();
    Ok(bytes.try_into().unwrap())
}

/// Helper structure pass around references to all the chips required for an
/// ECDSA verification.
struct ChipsRef<'a, F: Field, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize> {
    main_gate: &'a MainGate<F>,
    range_chip: &'a RangeChip<F>,
    ecc_chip: &'a GeneralEccChip<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    scalar_chip: &'a IntegerChip<secp256k1::Fq, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    base_chip: &'a IntegerChip<secp256k1::Fp, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ecdsa_chip: &'a EcdsaChip<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

impl<F: Field> SigCircuit<F> {
    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub fn min_num_rows(num_verif: usize) -> usize {
        // The values rows_ecc_chip_aux, rows_ecdsa_chip_verification and
        // rows_ecdsa_chip_verification have been obtained from log debugs while running
        // the tx circuit with max_txs=1. For example:
        // `RUST_LOG=debug RUST_BACKTRACE=1 cargo test tx_circuit_1tx_1max_tx --release
        // --all-features -- --nocapture`
        // The value rows_range_chip_table has been obtained by patching the halo2
        // library to report the number of rows used in the range chip table
        // region. TODO: Figure out a way to get these numbers automatically.
        let rows_range_chip_table = 295188;
        let rows_ecc_chip_aux = 226;
        let rows_ecdsa_chip_verification = 104471;
        let rows_signature_address_verify = 76;
        std::cmp::max(
            rows_range_chip_table,
            (rows_ecc_chip_aux + rows_ecdsa_chip_verification + rows_signature_address_verify)
                * num_verif,
        )
    }

    fn assign_aux(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        ecc_chip: &mut GeneralEccChip<Secp256k1Affine, F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(), Error> {
        ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
        ecc_chip.assign_aux(ctx, self.window_size, 2)?;
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
        let (sig_r, sig_s, _) = signature;

        let ChipsRef {
            main_gate: _,
            range_chip,
            ecc_chip,
            scalar_chip,
            ecdsa_chip,
            base_chip,
        } = chips;

        let integer_r = ecc_chip.new_unassigned_scalar(Value::known(*sig_r));
        let integer_s = ecc_chip.new_unassigned_scalar(Value::known(*sig_s));
        let msg_hash = ecc_chip.new_unassigned_scalar(Value::known(*msg_hash));

        let r_assigned = scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
        let s_assigned = scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
        let sig = AssignedEcdsaSig {
            r: r_assigned.clone(),
            s: s_assigned.clone(),
        };
        let r_le = integer_to_bytes_le(ctx, range_chip, &r_assigned)?;
        let s_le = integer_to_bytes_le(ctx, range_chip, &s_assigned)?;

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

        // Ref. spec SigCircuit 4. Verify the ECDSA signature
        ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)?;

        // assign the sign of y-coordinate which is `v`
        let v = base_chip.sign(ctx, pk_y)?;

        // TODO: Update once halo2wrong supports the following methods:
        // - `IntegerChip::assign_integer_from_bytes_le`
        // - `GeneralEccChip::assign_point_from_bytes_le`

        Ok(AssignedECDSA {
            pk_x_le,
            pk_y_le,
            msg_hash_le,
            r_le,
            s_le,
            v,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_rlc_le(
        &self,
        config: &SigCircuitConfig<F>,
        ctx: &mut RegionCtx<F>,
        chips: &ChipsRef<F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        name: &str,
        q_rlc: Selector,
        challenge: Value<F>,
        inputs_le: impl IntoIterator<Item = Term<F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let zero = chips.main_gate.assign_constant(ctx, F::ZERO)?;
        let columns = config.main_gate_config.advices();
        let inputs_le = inputs_le.into_iter().collect_vec();
        let inputs_be = iter::repeat_with(|| Term::assigned(zero.cell(), Value::known(F::ZERO)))
            .take(Integer::next_multiple_of(&inputs_le.len(), &columns.len()) - inputs_le.len())
            .chain(inputs_le.into_iter().rev())
            .collect_vec();

        let mut rlc = Value::known(F::ZERO);
        for (chunk_idx, chunk) in inputs_be.chunks_exact(columns.len()).enumerate() {
            ctx.enable(q_rlc)?;
            let assigned_rlc = ctx.assign_advice(|| "{name}_rlc[{chunk_idx}]", config.rlc, rlc)?;
            for ((idx, column), term) in (chunk_idx * chunk.len()..).zip(columns).zip(chunk) {
                let copied =
                    ctx.assign_advice(|| format!("{name}_byte[{idx}]"), column, term.value())?;
                if let Some(cell) = term.cell() {
                    ctx.constrain_equal(cell, copied.cell())?;
                }
            }
            if chunk_idx == 0 {
                ctx.constrain_equal(zero.cell(), assigned_rlc.cell())?;
            }
            rlc = iter::once(rlc)
                .chain(chunk.iter().map(|term| term.value()))
                .fold(Value::known(F::ZERO), |acc, input| acc * challenge + input);
            ctx.next();
        }

        let assigned_rlc = ctx.assign_advice(|| "{name}_rlc", config.rlc, rlc)?;
        ctx.next();

        Ok(assigned_rlc)
    }

    fn enable_keccak_lookup(
        &self,
        config: &SigCircuitConfig<F>,
        ctx: &mut RegionCtx<F>,
        is_address_zero: &AssignedCell<F, F>,
        pk_rlc: &AssignedCell<F, F>,
        pk_hash: &Word<AssignedCell<F, F>>,
    ) -> Result<(), Error> {
        let copy = |ctx: &mut RegionCtx<F>, name, column, assigned: &AssignedCell<F, F>| {
            let copied = ctx.assign_advice(|| name, column, assigned.value().copied())?;
            ctx.constrain_equal(assigned.cell(), copied.cell())?;
            Ok::<_, Error>(())
        };

        ctx.enable(config.q_keccak)?;
        copy(
            ctx,
            "is_address_zero",
            config.main_gate_config.advices()[0],
            is_address_zero,
        )?;
        copy(ctx, "pk_rlc", config.rlc, pk_rlc)?;
        copy(
            ctx,
            "pk_hash_lo",
            config.main_gate_config.advices()[1],
            &pk_hash.lo(),
        )?;
        copy(
            ctx,
            "pk_hash_hi",
            config.main_gate_config.advices()[2],
            &pk_hash.hi(),
        )?;
        ctx.next();

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_signature_verify(
        &self,
        config: &SigCircuitConfig<F>,
        ctx: &mut RegionCtx<F>,
        chips: &ChipsRef<F, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        sign_data: Option<&SignData>,
        assigned_ecdsa: &AssignedECDSA<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<AssignedSignatureVerify<F>, Error> {
        let main_gate = chips.main_gate;
        let range_chip = chips.range_chip;

        let (padding, sign_data) = match sign_data {
            Some(sign_data) => (false, sign_data.clone()),
            None => (true, SignData::default()),
        };

        let pk_be = pk_bytes_swap_endianness(&pk_bytes_le(&sign_data.pk));
        let mut pk_hash = (!padding).then(|| keccak256(&pk_be)).unwrap_or_default();
        pk_hash.reverse();

        let powers_of_256 = iter::successors(Some(F::ONE), |coeff| Some(F::from(256) * coeff))
            .take(16)
            .collect_vec();

        // Ref. spec SigCircuit 2. Verify that the first 20 bytes of the
        // pub_key_hash equal the address
        let (address_cells, pk_hash_cells) = {
            // Diagram of byte decomposition of little-endian pk_hash, and how address is built
            // from it:
            //
            // byte 0             15 16           20 21   32
            //      [ address_lo   ] [ address_hi  ] [     ]
            //      [ pk_hash_lo   ] [ pk_hash_hi          ]

            let pk_hash_lo_bytes = &pk_hash[..16];
            let pk_hash_hi_bytes = &pk_hash[16..];
            let pk_hash_lo = from_bytes::value::<F>(pk_hash_lo_bytes);
            let pk_hash_hi = from_bytes::value::<F>(pk_hash_hi_bytes);
            // Assign all bytes of pk_hash to cells which are range constrained to be 8 bits.  Then
            // constrain the lower 16 cell bytes to build the lo cell, and the higher 16 bytes to
            // build the hi cell.
            let (pk_hash_cell_lo, pk_hash_lo_cell_bytes) =
                range_chip.decompose(ctx, Value::known(pk_hash_lo), 8, 128)?;
            let (pk_hash_cell_hi, pk_hash_hi_cell_bytes) =
                range_chip.decompose(ctx, Value::known(pk_hash_hi), 8, 128)?;

            // Take the 20 lowest assigned byte cells of pk_hash and constrain them to build
            // address. We don't need lo/hi for an address so we concat assigned pk_hash bytes here.
            let powers_of_256_20_bytes =
                iter::successors(Some(F::ONE), |coeff| Some(F::from(256) * coeff))
                    .take(20)
                    .collect_vec();
            let pk_hash_bytes = &iter::empty()
                .chain(pk_hash_lo_cell_bytes)
                .chain(pk_hash_hi_cell_bytes)
                .collect_vec()[0..20];
            let (address_cell, _) = main_gate.decompose(
                ctx,
                &pk_hash_bytes
                    .iter()
                    .zip_eq(&powers_of_256_20_bytes)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;
            // let (address_cell_lo, _) = main_gate.decompose(
            //     ctx,
            //     &pk_hash_lo_cell_bytes
            //         .iter()
            //         .zip_eq(&powers_of_256)
            //         .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
            //         .collect_vec(),
            //     F::ZERO,
            //     |_, _| Ok(()),
            // )?;
            // let (address_cell_hi, _) = main_gate.decompose(
            //     ctx,
            //     &pk_hash_hi_cell_bytes
            //         .iter()
            //         .take(N_BYTES_ACCOUNT_ADDRESS - 16)
            //         .zip(&powers_of_256)
            //         .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
            //         .collect_vec(),
            //     F::ZERO,
            //     |_, _| Ok(()),
            // )?;

            (address_cell, Word::new([pk_hash_cell_lo, pk_hash_cell_hi]))
        };

        let is_address_zero = main_gate.is_zero(ctx, &address_cells)?;
        // let iz_zero_lo = main_gate.is_zero(ctx, &address_cells.lo())?;
        // let is_address_zero = main_gate.and(ctx, &iz_zero_lo, &iz_zero_hi)?;

        // Ref. spec SigCircuit 3. Verify that the signed message in the ecdsa_chip
        // corresponds to msg_hash
        let msg_hash_cells = {
            let msg_hash_lo_cell_bytes = &assigned_ecdsa.msg_hash_le[..16];
            let msg_hash_hi_cell_bytes = &assigned_ecdsa.msg_hash_le[16..];
            let (msg_hash_cell_lo, _) = main_gate.decompose(
                ctx,
                &msg_hash_lo_cell_bytes
                    .iter()
                    .zip_eq(&powers_of_256)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;
            let (msg_hash_cell_hi, _) = main_gate.decompose(
                ctx,
                &msg_hash_hi_cell_bytes
                    .iter()
                    .zip_eq(&powers_of_256)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;

            Word::new([msg_hash_cell_lo, msg_hash_cell_hi])
        };

        let pk_rlc = {
            let assigned_pk_le = iter::empty()
                .chain(&assigned_ecdsa.pk_y_le)
                .chain(&assigned_ecdsa.pk_x_le);
            let pk_le = iter::empty()
                .chain(sign_data.pk.y.to_bytes())
                .chain(sign_data.pk.x.to_bytes())
                .map(|byte| Value::known(F::from(byte as u64)));
            self.assign_rlc_le(
                config,
                ctx,
                chips,
                "pk_hash",
                config.q_rlc_keccak_input,
                challenges.keccak_input(),
                assigned_pk_le
                    .zip(pk_le)
                    .map(|(assigned, byte)| Term::assigned(assigned.cell(), byte)),
            )?
        };

        let (r, s) = {
            let r_lo_cell_bytes = &assigned_ecdsa.r_le[..16];
            let r_hi_cell_bytes = &assigned_ecdsa.r_le[16..];
            let s_lo_cell_bytes = &assigned_ecdsa.s_le[..16];
            let s_hi_cell_bytes = &assigned_ecdsa.s_le[16..];

            let (r_cell_lo, _) = main_gate.decompose(
                ctx,
                &r_lo_cell_bytes
                    .iter()
                    .zip_eq(&powers_of_256)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;
            let (r_cell_hi, _) = main_gate.decompose(
                ctx,
                &r_hi_cell_bytes
                    .iter()
                    .zip_eq(&powers_of_256)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;

            let (s_cell_lo, _) = main_gate.decompose(
                ctx,
                &s_lo_cell_bytes
                    .iter()
                    .zip_eq(&powers_of_256)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;
            let (s_cell_hi, _) = main_gate.decompose(
                ctx,
                &s_hi_cell_bytes
                    .iter()
                    .zip_eq(&powers_of_256)
                    .map(|(cell, coeff)| maingate::Term::Assigned(cell, *coeff))
                    .collect_vec(),
                F::ZERO,
                |_, _| Ok(()),
            )?;

            (
                Word::new([r_cell_lo, r_cell_hi]),
                Word::new([s_cell_lo, s_cell_hi]),
            )
        };

        // TODO fix it
        let is_valid = main_gate.and(ctx, &pk_rlc, &pk_rlc)?;

        self.enable_keccak_lookup(config, ctx, &is_address_zero, &pk_rlc, &pk_hash_cells)?;
        Ok(AssignedSignatureVerify {
            address: address_cells,
            msg_hash: msg_hash_cells,
            r,
            s,
            v: assigned_ecdsa.v.clone(),
            is_valid,
        })
    }

    pub(crate) fn assign(
        &self,
        config: &SigCircuitConfig<F>,
        layouter: &mut impl Layouter<F>,
        signatures: &[SignData],
        challenges: &Challenges<Value<F>>,
    ) -> Result<Vec<AssignedSignatureVerify<F>>, Error> {
        if signatures.len() > self.max_verif {
            error!(
                "signatures.len() = {} > max_verif = {}",
                signatures.len(),
                self.max_verif
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
        let base_chip = cloned_ecc_chip.base_field_chip();

        layouter.assign_region(
            || "ecc chip aux",
            |region| {
                let mut ctx = RegionCtx::new(region, 0);
                self.assign_aux(&mut ctx, &mut ecc_chip)?;
                log::debug!("ecc chip aux: {} rows", ctx.offset());
                Ok(())
            },
        )?;

        let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());

        let chips = ChipsRef {
            main_gate: &main_gate,
            range_chip: &range_chip,
            ecc_chip: &ecc_chip,
            scalar_chip,
            base_chip,
            ecdsa_chip: &ecdsa_chip,
        };

        let assigned_ecdsas = layouter.assign_region(
            || "ecdsa chip verification",
            |region| {
                let mut assigned_ecdsas = Vec::new();
                let mut ctx = RegionCtx::new(region, 0);
                for i in 0..self.max_verif {
                    let signature = if i < signatures.len() {
                        signatures[i].clone()
                    } else {
                        // padding (enabled when address == 0)
                        SignData::default()
                    };
                    let assigned_ecdsa = self.assign_ecdsa(&mut ctx, &chips, &signature)?;
                    assigned_ecdsas.push(assigned_ecdsa);
                }
                log::debug!("ecdsa chip verification: {} rows", ctx.offset());
                Ok(assigned_ecdsas)
            },
        )?;

        let assigned_sig_verifs = layouter.assign_region(
            || "signature address verify",
            |region| {
                let mut assigned_sig_verifs = Vec::new();
                let mut ctx = RegionCtx::new(region, 0);
                for (i, assigned_ecdsa) in assigned_ecdsas.iter().enumerate() {
                    let sign_data = signatures.get(i); // None when padding (enabled when address == 0)
                    let assigned_sig_verif = self.assign_signature_verify(
                        config,
                        &mut ctx,
                        &chips,
                        sign_data,
                        assigned_ecdsa,
                        challenges,
                    )?;
                    assigned_sig_verifs.push(assigned_sig_verif);
                }
                log::debug!("signature address verify: {} rows", ctx.offset());
                Ok(assigned_sig_verifs)
            },
        )?;

        layouter.assign_region(
            || "expose sig table",
            |mut region| {
                // export as a lookup table
                for (idx, assigned_sig_verif) in assigned_sig_verifs.iter().enumerate() {
                    region.assign_fixed(
                        || "assign sig_table selector",
                        config.sig_table.q_enable,
                        idx,
                        || Value::known(F::ONE),
                    )?;

                    assigned_sig_verif.v.copy_advice(
                        || "v",
                        &mut region,
                        config.sig_table.sig_v,
                        idx,
                    )?;

                    assigned_sig_verif.r.lo().copy_advice(
                        || "r_lo",
                        &mut region,
                        config.sig_table.sig_r.lo(),
                        idx,
                    )?;

                    assigned_sig_verif.r.hi().copy_advice(
                        || "r_hi",
                        &mut region,
                        config.sig_table.sig_r.lo(),
                        idx,
                    )?;

                    assigned_sig_verif.s.lo().copy_advice(
                        || "s_lo",
                        &mut region,
                        config.sig_table.sig_s.lo(),
                        idx,
                    )?;
                    assigned_sig_verif.s.hi().copy_advice(
                        || "s_hi",
                        &mut region,
                        config.sig_table.sig_s.hi(),
                        idx,
                    )?;

                    assigned_sig_verif.address.copy_advice(
                        || "address",
                        &mut region,
                        config.sig_table.recovered_addr,
                        idx,
                    )?;

                    assigned_sig_verif.is_valid.copy_advice(
                        || "is_valid",
                        &mut region,
                        config.sig_table.is_valid,
                        idx,
                    )?;

                    assigned_sig_verif.msg_hash.lo().copy_advice(
                        || "msg hash lo",
                        &mut region,
                        config.sig_table.msg_hash.lo(),
                        idx,
                    )?;
                    assigned_sig_verif.msg_hash.hi().copy_advice(
                        || "msg hash hi",
                        &mut region,
                        config.sig_table.msg_hash.hi(),
                        idx,
                    )?;
                }
                Ok(())
            },
        )?;

        Ok(assigned_sig_verifs)
    }
}
